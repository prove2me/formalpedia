-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_hasCoverBy_one_50abedecca77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:10.152377+00:00
-- url     : https://prove2.me/submissions/c118e4ad-9c5b-48de-b0bc-cef0cb419342

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne

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
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) {Pr : Ω → Prop} (h : Pr 1) :
    HasCoverBy y c Pr :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => h⟩
end GroundTheory.Heights₂.Heights.LowerBoundFree
