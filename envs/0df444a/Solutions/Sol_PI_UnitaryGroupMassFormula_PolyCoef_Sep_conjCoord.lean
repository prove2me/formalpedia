-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.Sep.conjCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:36.847639+00:00
-- url     : https://prove2.me/submissions/3d835bad-26cd-4142-b06f-7dfb8afcdc71

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_entry

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
theorem _root_.solution {N : ℕ} (i j : Fin N) :
    Sep (fun g : UG N => star ((g : Matrix (Fin N) (Fin N) ℂ) i j)) := by
  refine ⟨Fin N, inferInstance, fun k h => (h : Matrix (Fin N) (Fin N) ℂ) k i,
    fun k y => star ((y : Matrix (Fin N) (Fin N) ℂ) k j), fun k => IsPD.entry k i,
    fun k => (coordC k j).continuous.star, fun h y => ?_⟩
  show star ((star (h : Matrix (Fin N) (Fin N) ℂ) * (y : Matrix (Fin N) (Fin N) ℂ)) i j) = _
  rw [Matrix.mul_apply]
  simp [Matrix.star_apply]
end Sep
end PI.UnitaryGroupMassFormula.PolyCoef
