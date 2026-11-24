-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.theta_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:00.852665+00:00
-- url     : https://prove2.me/submissions/1a740619-369a-40e7-8f87-9d0dacede96e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) : IsIntegral ℚ (UnitDetRootDefs.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C ((a : ℚ) * c), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    linear_combination theta_sq hok
end PI.UnitaryGroupMassFormula.UnitDetRoot
