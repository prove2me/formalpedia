-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsHerm_h_2fda21fa2b8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:17.394594+00:00
-- url     : https://prove2.me/submissions/f086ac1e-4a8b-4658-8164-6a3186f6838e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagIndices_InstFintypeFlIdx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (a : K → ℤ) (z : (Σ k, ι k) → ℂ) : (fsHerm ι a).h z = refNorm a z := rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree
