-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.algebraMap_thetaO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:09.674118+00:00
-- url     : https://prove2.me/submissions/42de3412-4649-40b8-b8d3-3323323bb902

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) :
    algebraMap (𝓞 (KF b d)) ℂ (thetaO hok) = UnitDetRootDefs.cmTheta b d := by
  rfl
end PI.UnitaryGroupMassFormula.UnitDetRoot
