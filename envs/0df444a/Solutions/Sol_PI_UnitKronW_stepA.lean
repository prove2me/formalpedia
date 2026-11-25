-- Prove2me | solution 1 for PI.UnitKronW.stepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:34.490987+00:00
-- url     : https://prove2.me/submissions/478a492d-b638-4bd6-a3ec-df1688f75f72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development
import Definitions.Def_Lemmata_GeneralBFactRightBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_PosDefFormNeZero
import Theorems.Thm_PI_UnitKronW_form_pres
import Theorems.Thm_PI_UnitKronW_posDef_form_ne_zero
import Theorems.Thm_PI_UnitKronW_exists_eigenvector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution : StepA := by
  intro k H G hH hG μ hμ
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector G μ hμ
  have h := form_pres hG v v
  rw [hv, Matrix.mulVec_smul, star_smul] at h
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
  have hq := posDef_form_ne_zero hH hv0
  have h1 : star μ * μ = 1 := by
    have : (star μ * μ) * (star v ⬝ᵥ (H *ᵥ v)) = 1 * (star v ⬝ᵥ (H *ᵥ v)) := by
      rw [one_mul]; linear_combination h
    exact mul_right_cancel₀ hq this
  have h2 : Complex.normSq μ = 1 := by
    have := congrArg Complex.re h1
    rw [Complex.star_def, mul_comm, Complex.mul_conj] at this
    simpa using this
  rw [Complex.normSq_eq_norm_sq] at h2
  nlinarith [norm_nonneg μ]
end PI.UnitKronW
