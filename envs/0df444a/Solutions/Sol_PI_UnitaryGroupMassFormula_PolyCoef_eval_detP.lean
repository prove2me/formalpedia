-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.eval_detP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:21.565109+00:00
-- url     : https://prove2.me/submissions/55a0709b-871d-4526-b42f-125017d2c328

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_mapX_eval

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
theorem _root_.solution {N : ℕ} (g : UG N) :
    MvPolynomial.eval (ent g) (detP N) = (g : Matrix (Fin N) (Fin N) ℂ).det := by
  unfold detP
  rw [RingHom.map_det, mapX_eval]
end PI.UnitaryGroupMassFormula.PolyCoef
