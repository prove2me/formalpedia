-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.theta_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:12.473498+00:00
-- url     : https://prove2.me/submissions/88ee55ae-ed64-4c1e-a427-f3a8b60f17b6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Lemmata_GeneralBFactLeftTer_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot

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
theorem _root_.solution {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) :
    UnitDetRootDefs.cmTheta b d ^ 2 = b * UnitDetRootDefs.cmTheta b d - (a : ℂ) * c := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have h4 : (4 : ℂ) * a * c = b ^ 2 + d := by exact_mod_cast hok.1
  simp only [UnitDetRootDefs.cmTheta]
  linear_combination (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) / 4) * Complex.I_mul_I
    - (1 / 4 : ℂ) * hs + (1 / 4 : ℂ) * h4
end PI.UnitaryGroupMassFormula.UnitDetRoot
