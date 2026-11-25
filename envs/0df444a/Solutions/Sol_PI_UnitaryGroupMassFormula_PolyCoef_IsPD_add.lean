-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.IsPD.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:49:02.675326+00:00
-- url     : https://prove2.me/submissions/4286f259-458e-4699-ba9d-0c4b89b21a26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_eval_detP

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
namespace IsPD
theorem _root_.solution {N : ℕ} {f f' : UG N → ℂ} (hf : IsPD f) (hf' : IsPD f') : IsPD (fun g => f g + f' g) := by
  obtain ⟨k, P, hP⟩ := hf
  obtain ⟨k', P', hP'⟩ := hf'
  refine ⟨k + k', P * detP N ^ k' + P' * detP N ^ k, fun g => ?_⟩
  simp only [map_add, map_mul, map_pow, eval_detP, ← hP g, ← hP' g]
  ring
end IsPD
end PI.UnitaryGroupMassFormula.PolyCoef
