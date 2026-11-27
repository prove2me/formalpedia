-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_smoothRep_h_a567715cdacf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:43.567545+00:00
-- url     : https://prove2.me/submissions/82068062-3341-4c1f-ad35-fb44c22bf6c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_EqZeroOfIsIsoSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [instance] CxModel.top CxModel.compact CxModel.t2
variable {P : Ideal (MRing ι)} {d : ℕ}
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {P : Ideal (MRing ι)} (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    (smoothRep P A).h z = A.h z := by
  classical
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.2 z hz
  · rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree
