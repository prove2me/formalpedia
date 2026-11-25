-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.unipotent_radical_contracting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:46:23.036179+00:00
-- url     : https://prove2.me/submissions/0653552d-b3f1-4560-a2f7-0fc43ffcfc66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_mul_dS_inv
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_dS_conj_S_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_norm_dS_conj_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution : NContract := by
  intro k r z _ n hn ε hε
  have hM : 0 ≤ ∑ i, ∑ j, ‖n i j‖ := by positivity
  have hs0 : 0 < min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) := lt_min one_pos (div_pos hε (by linarith))
  have hs1 : min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) ≤ 1 := min_le_left _ _
  refine ⟨dS k r (min 1 (ε / (∑ i, ∑ j, ‖n i j‖ + 1))),
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (dS_mul_dS_inv hs0.ne')),
    fun g => dS_conj_S_iff hs0.ne' g, fun i j => ?_⟩
  have hentry : ‖n i j‖ ≤ ∑ i, ∑ j, ‖n i j‖ :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (n i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖n i j‖)
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
  calc ‖(dS k r _ * n * (dS k r _)⁻¹ - 1) i j‖ ≤ _ * ‖n i j‖ := norm_dS_conj_le hs0 hs1 hn i j
    _ ≤ (ε / (∑ i, ∑ j, ‖n i j‖ + 1)) * ∑ i, ∑ j, ‖n i j‖ :=
        mul_le_mul (min_le_right _ _) hentry (norm_nonneg _) (div_pos hε (by linarith)).le
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
end PI.QuotSetU.UnitaryGroupMassFormula.SW
