-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.altE_natsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:17.165585+00:00
-- url     : https://prove2.me/submissions/bf27bd29-a9b3-4c76-80ac-efed136cde11

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (H : UnitDetRootDefs.Sesq V) (k : ℕ) (x y : V) :
    UnitDetRootDefs.altE H ((k : ℂ) • x) y = UnitDetRootDefs.altE H x ((k : ℂ) • y) := by
  simp [UnitDetRootDefs.altE, LinearMap.map_smulₛₗ]
end PI.UnitaryGroupMassFormula.UnitDetRoot
