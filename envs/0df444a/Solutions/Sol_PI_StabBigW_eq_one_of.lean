-- Prove2me | solution 1 for PI.StabBigW.eq_one_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:30.147808+00:00
-- url     : https://prove2.me/submissions/848d0598-13e1-4b3c-a5b3-054926f87d0b

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_tau_val
import Theorems.Thm_PI_StabBigW_wI_val
import Theorems.Thm_PI_StabBigW_dd_ne
import Theorems.Thm_PI_StabBigW_g_col_out
import Theorems.Thm_PI_StabBigW_mul_g_out
import Theorems.Thm_PI_StabBigW_g_mul_out
import Theorems.Thm_PI_StabBigW_mul_g_mid
import Theorems.Thm_PI_StabBigW_vec_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
private theorem tau_tau_lemma (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have h1 := tau_val (k := k) (r := r) i
  have h2 := tau_val (k := k) (r := r) (tau k r i)
  have hi := i.isLt
  ext
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [if_pos hc] at h1
    have hc2 : (tau k r i).val < r ∨ r + k < (tau k r i).val := by omega
    rw [if_pos hc2] at h2
    omega
  · rw [if_neg hc] at h1
    have hc2 : ¬ ((tau k r i).val < r ∨ r + k < (tau k r i).val) := by omega
    rw [if_neg hc2] at h2
    omega
end PI.StabBigW
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace PI.StabBigW
theorem _root_.solution {c : Fin r → ℂ} {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hc : ∀ a, c a ≠ 0) (hL : μ * L = 1)
    {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : UT k r a) (hb : UT k r b) (E : a * bigCell k r c μ = bigCell k r c μ * b) : a = 1 := by
  ext i m
  rw [Matrix.one_apply]
  have hil := i.isLt
  have hml := m.isLt
  by_cases hmi : m.val ≤ i.val ∨ (r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ m.val ∧ m.val ≤ r + k)
  · exact ha i m hmi
  have hne : ¬ i = m := fun h => hmi (Or.inl (by subst h; exact le_refl _))
  rw [if_neg hne]
  by_cases hm : m.val < r ∨ r + k < m.val
  · have htm := tau_val (k := k) (r := r) m
    rw [if_pos hm] at htm
    have hjo : (tau k r m).val < r ∨ r + k < (tau k r m).val := by omega
    have E1 := congrFun (congrFun E i) (tau k r m)
    rw [mul_g_out _ _ _ i _ hjo, tau_tau_lemma] at E1
    have hd := dd_ne hc (tau k r m) hjo
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [g_mul_out _ _ _ i _ hi] at E1
      have hti := tau_val (k := k) (r := r) i
      rw [if_pos hi] at hti
      have hb0 : b (tau k r i) (tau k r m) = 0 := by
        rw [hb (tau k r i) (tau k r m) (Or.inl (by omega)),
          if_neg (fun h => by have := congrArg Fin.val h; omega)]
      rw [hb0, mul_zero] at E1
      exact (mul_eq_zero.mp E1).resolve_right hd
    · rw [Matrix.mul_apply] at E1
      have hz : ∑ n, bigCell k r c μ i n * b n (tau k r m) = 0 := by
        apply Finset.sum_eq_zero
        intro n _
        have hnl := n.isLt
        by_cases hn : n.val < r ∨ r + k < n.val
        · have htn := tau_val (k := k) (r := r) n
          rw [if_pos hn] at htn
          have hin : ¬ i = tau k r n := fun h => by have := congrArg Fin.val h; omega
          rw [g_col_out _ _ i n hn, if_neg hin, zero_mul]
        · rw [hb n (tau k r m) (Or.inl (by omega)),
            if_neg (fun h => by have := congrArg Fin.val h; omega), mul_zero]
      rw [hz] at E1
      exact (mul_eq_zero.mp E1).resolve_right hd
  · have hi : i.val < r ∨ r + k < i.val := by omega
    have emw : m = wI k r ⟨m.val - r, by omega⟩ := Fin.ext (by simp only [wI_val]; omega)
    have hti := tau_val (k := k) (r := r) i
    rw [if_pos hi] at hti
    have hv : (fun s => a i (wI k r s)) = 0 := by
      apply vec_zero hL
      intro t
      have htl := t.isLt
      show ∑ s, a i (wI k r s) * μ s t = 0
      have E1 := congrFun (congrFun E i) (wI k r t)
      rw [mul_g_mid, g_mul_out _ _ _ i _ hi] at E1
      rw [E1, hb (tau k r i) (wI k r t) (Or.inl (by simp only [wI_val]; omega)),
        if_neg (fun h => by
          have e := congrArg Fin.val h
          simp only [wI_val] at e
          omega), mul_zero]
    rw [emw]
    exact congrFun hv _
end PI.StabBigW
