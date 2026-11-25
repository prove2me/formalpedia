-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_mul_b675f81d17d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:47.802358+00:00
-- url     : https://prove2.me/submissions/bae61853-8b36-4dd5-8049-3850ff9ec84a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt

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
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution (z : Cone n ℂ) (f g : MvPolynomial (Coord n) ℤ) :
    evalCone z (f * g) = evalCone z f * evalCone z g := by
  simp [evalCone, eval₂_mul]
end GroundTheory.Heights₂.Heights.MonomialMap
