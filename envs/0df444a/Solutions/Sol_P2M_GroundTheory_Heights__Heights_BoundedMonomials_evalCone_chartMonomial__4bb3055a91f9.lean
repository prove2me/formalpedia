-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_chartMonomial__4bb3055a91f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:45.426211+00:00
-- url     : https://prove2.me/submissions/540960d8-3260-44b4-b729-ef13a1f16e10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution {F : Type*} [CommRing F] (z : Cone n F)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod]
end GroundTheory.Heights₂.Heights.BoundedMonomials
