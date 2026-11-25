-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_evalCone_pow_7a3509d44448
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:26.315478+00:00
-- url     : https://prove2.me/submissions/44a699a3-22cc-489e-8d1d-91f59a88071b

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
theorem _root_.solution (z : Cone n ℂ) (f : MvPolynomial (Coord n) ℤ) (m : ℕ) :
    evalCone z (f ^ m) = evalCone z f ^ m := by
  simp only [evalCone, eval₂_pow]
end GroundTheory.Heights₂.Heights.MonomialMapNorm
