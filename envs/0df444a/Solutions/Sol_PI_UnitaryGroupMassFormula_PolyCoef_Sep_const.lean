-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.Sep.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:38.764284+00:00
-- url     : https://prove2.me/submissions/339ccf9b-41b2-41cd-9f72-e512080af441

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.PolyCoef
namespace Sep
theorem _root_.solution {N : ℕ} (c : ℂ) : Sep (fun _ : UG N => c) :=
  ⟨Unit, inferInstance, fun _ _ => c, fun _ _ => 1, fun _ => IsPD.const c, fun _ => continuous_const,
    fun h y => by simp⟩
end Sep
end PI.UnitaryGroupMassFormula.PolyCoef
