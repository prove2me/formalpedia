-- Prove2me | solution 1 for PI.StabBigW.g_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:49.490939+00:00
-- url     : https://prove2.me/submissions/c6379f27-df86-4432-ad2b-65e9e1f792da

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Theorems.Thm_PI_StabBigW_tau_val
import Theorems.Thm_PI_StabBigW_wI_val
import Theorems.Thm_PI_StabBigW_wI_inj
import Theorems.Thm_PI_StabBigW_dd_tau
import Theorems.Thm_PI_StabBigW_g_col_out
import Theorems.Thm_PI_StabBigW_g_mid_col
import Theorems.Thm_PI_StabBigW_g_wI
import Theorems.Thm_PI_StabBigW_mul_g_out
import Theorems.Thm_PI_StabBigW_mul_g_mid
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
theorem _root_.solution {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {μ L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hL : L * μ = 1) : bigCell k r (fun a => star (c a)) L * bigCell k r c μ = 1 := by
  ext i j
  rw [Matrix.one_apply]
  have hil := i.isLt
  have hjl := j.isLt
  by_cases hj : j.val < r ∨ r + k < j.val
  · have ht := tau_val (k := k) (r := r) j
    rw [if_pos hj] at ht
    have hto : (tau k r j).val < r ∨ r + k < (tau k r j).val := by omega
    rw [mul_g_out _ _ _ i j hj, g_col_out _ _ i (tau k r j) hto, tau_tau_lemma, ite_mul, zero_mul,
      dd_tau hc j hj]
  · have ej : j = wI k r ⟨j.val - r, by omega⟩ := Fin.ext (by simp only [wI_val]; omega)
    rw [ej, mul_g_mid]
    by_cases hi : i.val < r ∨ r + k < i.val
    · have hne : ¬ i = wI k r ⟨j.val - r, by omega⟩ := fun h => by
        have e := congrArg Fin.val h
        simp only [wI_val] at e
        omega
      rw [if_neg hne]
      apply Finset.sum_eq_zero
      intro s _
      have hs := s.isLt
      rw [g_mid_col _ _ i _ (by simp only [wI_val]; omega) (by simp only [wI_val]; omega) hi, zero_mul]
    · have ei : i = wI k r ⟨i.val - r, by omega⟩ := Fin.ext (by simp only [wI_val]; omega)
      rw [ei]
      simp only [g_wI]
      rw [← Matrix.mul_apply, hL, Matrix.one_apply]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (by rw [h1]) h2
      · exact absurd (wI_inj h2) h1
      · rfl
end PI.StabBigW
