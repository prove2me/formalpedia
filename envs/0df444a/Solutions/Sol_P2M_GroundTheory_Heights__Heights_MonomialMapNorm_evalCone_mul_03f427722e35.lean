-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_mul_03f427722e35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:24.907796+00:00
-- url     : https://prove2.me/submissions/42ee9371-dda2-4efd-ac54-df372278575b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMapNorm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution (z : Cone n ℂ) (f f' : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * f') = evalCone z f * evalCone z f' := by
  simp only [evalCone, eval₂_mul]
end GroundTheory.Heights₂.Heights.MonomialMapNorm
