-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.Sep.coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:03.815052+00:00
-- url     : https://prove2.me/submissions/160eda6e-9e40-4e3d-bee7-e1bd971d674c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_conjEntry

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
theorem _root_.solution {N : ℕ} (i j : Fin N) : Sep (fun g : UG N => (g : Matrix (Fin N) (Fin N) ℂ) i j) := by
  refine ⟨Fin N, inferInstance, fun k h => star ((h : Matrix (Fin N) (Fin N) ℂ) k i),
    fun k y => (y : Matrix (Fin N) (Fin N) ℂ) k j, fun k => IsPD.conjEntry k i,
    fun k => (coordC k j).continuous, fun h y => ?_⟩
  show (star (h : Matrix (Fin N) (Fin N) ℂ) * (y : Matrix (Fin N) (Fin N) ℂ)) i j = _
  rw [Matrix.mul_apply]
  simp [Matrix.star_apply]
end Sep
end PI.UnitaryGroupMassFormula.PolyCoef
