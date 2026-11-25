-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isLive_of_point_532e268d2994
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:38.637455+00:00
-- url     : https://prove2.me/submissions/b288588a-c2dd-4cc0-8682-2a1d3b103a16

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
variable (P : ArithVariety n)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.MonomialMapNorm
theorem _root_.solution {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)}
    (hcz : ∀ k, z k (c k) ≠ 0) : P.IsLive c := fun k hk ↦
  hcz k (by simpa only [evalCone, eval₂_X] using hz.2 _ hk)
end GroundTheory.Heights₂.Heights.MonomialMapNorm
