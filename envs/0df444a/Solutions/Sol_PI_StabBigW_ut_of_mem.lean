-- Prove2me | solution 1 for PI.StabBigW.ut_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:21.516058+00:00
-- url     : https://prove2.me/submissions/300312d8-7d89-4011-bcf1-072140350820

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_tau_val
import Theorems.Thm_PI_StabBigW_hpk_col
import Theorems.Thm_PI_StabBigW_adj_apply
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
private theorem sgn_tau' (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  have h1 := tau_val (k := k) (r := r) i
  have hi := i.isLt
  unfold sgn
  by_cases hc : i.val < r ∨ r + k < i.val
  · rw [if_pos hc] at h1
    rw [if_neg (by omega : ¬ (tau k r i).val = r + k), if_neg (by omega : ¬ i.val = r + k)]
  · rw [if_neg hc] at h1
    rw [h1]
private theorem Hpk_mul_self' : Hpk k r * Hpk k r = 1 := by
  ext p q
  have e1 : ∀ m, Hpk k r m q = if m = tau k r q then sgn k r q else 0 := fun m => hpk_col m q
  rw [Matrix.mul_apply]
  simp only [e1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hpk_col, tau_tau_lemma, Matrix.one_apply]
  split_ifs with h
  · rw [sgn_tau']
    unfold sgn
    split_ifs <;> norm_num
  · simp
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
theorem _root_.solution {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : UT k r a := by
  unfold Nset at ha
  rw [Set.mem_setOf_eq] at ha
  obtain ⟨hU, hcol, hmid⟩ := ha
  have hU' : aᴴ * Hpk k r * a = Hpk k r := hU
  have hba : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', Hpk_mul_self']
  have hab : a * (Hpk k r * aᴴ * Hpk k r) = 1 := by
    rw [← Matrix.inv_eq_left_inv hba]
    exact Matrix.mul_nonsing_inv a (Matrix.isUnit_det_of_left_inverse hba)
  have hcolv : ∀ p m : Fin (2 * r + k + 1), m.val < r → m.val ≤ p.val →
      a p m = if p = m then 1 else 0 := by
    intro p m hm hle
    have e := hcol ⟨m.val, hm⟩ p hle
    rwa [show eI k r ⟨m.val, hm⟩ = m from Fin.ext rfl] at e
  have hsg : ∀ m : Fin (2 * r + k + 1), m.val ≠ r + k → sgn k r m = 1 := by
    intro m hm
    unfold sgn
    rw [if_neg hm]
  have key : ∀ q : ℕ, ∀ i j : Fin (2 * r + k + 1), j.val = q → r + k < q → q ≤ i.val →
      a i j = if i = j then 1 else 0 := by
    intro q
    refine Nat.strong_induction_on q ?_
    intro q IH i j hjq hq hqi
    have hil := i.isLt
    have hjl := j.isLt
    have hj' : j.val < r ∨ r + k < j.val := Or.inr (by omega)
    have htj := tau_val (k := k) (r := r) j
    rw [if_pos hj'] at htj
    have hbjj : (Hpk k r * aᴴ * Hpk k r) j j = 1 := by
      rw [adj_apply, hcolv (tau k r j) (tau k r j) (by omega) le_rfl, if_pos rfl, hsg j (by omega)]
      simp
    have hsum : ∑ m, a i m * (Hpk k r * aᴴ * Hpk k r) m j = a i j := by
      rw [Finset.sum_eq_single j]
      · rw [hbjj, mul_one]
      · intro m _ hmj
        have hml := m.isLt
        by_cases hm1 : m.val ≤ r + k
        · have ha0 : a i m = 0 := by
            by_cases hm2 : m.val < r
            · rw [hcolv i m hm2 (by omega), if_neg (fun h => by have := congrArg Fin.val h; omega)]
            · rw [hmid i m (by omega) hm1 (by omega),
                if_neg (fun h => by have := congrArg Fin.val h; omega)]
          rw [ha0, zero_mul]
        · by_cases hm3 : m.val < j.val
          · rw [IH m.val (by omega) i m rfl (by omega) (by omega),
              if_neg (fun h => by have := congrArg Fin.val h; omega), zero_mul]
          · have hmo : m.val < r ∨ r + k < m.val := Or.inr (by omega)
            have htm := tau_val (k := k) (r := r) m
            rw [if_pos hmo] at htm
            have hmj' : j.val < m.val := by
              rcases Nat.lt_or_ge j.val m.val with h | h
              · exact h
              · exact absurd (Fin.ext (by omega)) hmj
            rw [adj_apply, hcolv (tau k r j) (tau k r m) (by omega) (by omega),
              if_neg (fun h => by have := congrArg Fin.val h; omega)]
            simp only [star_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have E := congrFun (congrFun hab i) j
    rw [Matrix.mul_apply, Matrix.one_apply, hsum] at E
    exact E
  unfold UT
  intro i j hij
  have hil := i.isLt
  have hjl := j.isLt
  by_cases h1 : j.val < r
  · exact hcolv i j h1 (by omega)
  · by_cases h2 : j.val ≤ r + k
    · exact hmid i j (by omega) h2 (by omega)
    · exact key j.val i j rfl (by omega) (by omega)
end PI.StabBigW
