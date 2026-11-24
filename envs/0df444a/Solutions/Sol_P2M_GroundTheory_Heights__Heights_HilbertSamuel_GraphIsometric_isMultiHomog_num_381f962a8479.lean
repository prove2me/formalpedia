-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_isMultiHomog_num_381f962a8479
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:27.696346+00:00
-- url     : https://prove2.me/submissions/8593ea06-923f-47f3-8d23-a75893427395

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_wh_lin_53ec7387a784
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
theorem _root_.solution [DecidableEq K] (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) :
    IsMultiHomog (num A j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inl k) 1 + (-a k).toNat • Pi.single (Sum.inr k) 1)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((wh_lin A ⟨k, j k⟩).pow _).mul ((isWeightedHomogeneous_X ℤ _ _).pow _)
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
