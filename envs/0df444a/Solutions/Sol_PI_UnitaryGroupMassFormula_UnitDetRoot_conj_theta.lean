-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.conj_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:19.494678+00:00
-- url     : https://prove2.me/submissions/79542bcc-c2ca-458b-add0-1513f00dc087

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
theorem _root_.solution (b : ℤ) (d : ℕ) : conj (UnitDetRootDefs.cmTheta b d) = (b : ℂ) - UnitDetRootDefs.cmTheta b d := by
  simp only [UnitDetRootDefs.cmTheta, map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast,
    map_ofNat]
  ring
end PI.UnitaryGroupMassFormula.UnitDetRoot
