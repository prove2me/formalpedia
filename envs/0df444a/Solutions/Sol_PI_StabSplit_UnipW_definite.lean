-- Prove2me | solution 1 for PI.StabSplit.UnipW.definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:45.904344+00:00
-- url     : https://prove2.me/submissions/87747f07-cc60-47c7-9bf6-1fc045257246

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
import Theorems.Thm_PI_StabSplit_UnipW_herm_conjW
import Theorems.Thm_PI_StabSplit_UnipW_herm_self_re
import Theorems.Thm_PI_StabSplit_UnipW_sum_W_nonneg
import Theorems.Thm_PI_StabSplit_UnipW_herm_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {k r : ℕ} {y z : Fin (2 * r + k + 1) → ℂ} (hy : perpX k r y) (hz : inWb k r z)
    (hT : 0 < Tz k r z) (h1 : herm (Hpk k r) y y = 0) (h2 : herm (Hpk k r) y z = 0) : inX k r y := by
  have hzp : perpX k r z := fun i hi => hz i (Or.inr hi)
  have hzL : z (Lk k r) ≠ 0 := by
    intro h0
    have hnn : 0 ≤ (herm (Hpk k r) z z).re := by rw [herm_self_re hzp h0]; exact sum_W_nonneg z
    unfold Tz at hT; linarith
  set c := y (Lk k r) / z (Lk k r) with hc
  have hwp : perpX k r (y - c • z) := fun i hi => by simp [hy i hi, hzp i hi]
  have hwL : (y - c • z) (Lk k r) = 0 := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc, div_mul_cancel₀ _ hzL, sub_self]
  have hzy : herm (Hpk k r) z y = 0 := by rw [herm_conjW hy hzp, h2, star_zero]
  have hexp : herm (Hpk k r) (y - c • z) (y - c • z) = (Complex.normSq c : ℂ) * herm (Hpk k r) z z := by
    rw [herm_expand, h1, h2, hzy, Complex.star_def, Complex.mul_conj]; ring
  have hre : (herm (Hpk k r) (y - c • z) (y - c • z)).re = -(Complex.normSq c * Tz k r z) := by
    rw [hexp, Complex.re_ofReal_mul]; unfold Tz; ring
  have hnn : 0 ≤ (herm (Hpk k r) (y - c • z) (y - c • z)).re := by
    rw [herm_self_re hwp hwL]; exact sum_W_nonneg _
  have hc0 : Complex.normSq c = 0 := by
    by_contra hne
    have hpos : 0 < Complex.normSq c := lt_of_le_of_ne (Complex.normSq_nonneg c) (Ne.symm hne)
    have := mul_pos hpos hT
    linarith
  have hyL : y (Lk k r) = 0 := by
    have h0 := Complex.normSq_eq_zero.mp hc0
    rw [hc, div_eq_zero_iff] at h0
    exact h0.resolve_right hzL
  have hsum := herm_self_re hy hyL
  rw [h1, Complex.zero_re] at hsum
  intro i hi
  by_cases hik : r + k < i.val
  · exact hy i hik
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
      split_ifs <;> [exact Complex.normSq_nonneg _; exact le_refl _])).mp hsum.symm i (Finset.mem_univ _)
    rw [if_pos ⟨hi, by omega⟩] at hall
    exact Complex.normSq_eq_zero.mp hall
end PI.StabSplit.UnipW
