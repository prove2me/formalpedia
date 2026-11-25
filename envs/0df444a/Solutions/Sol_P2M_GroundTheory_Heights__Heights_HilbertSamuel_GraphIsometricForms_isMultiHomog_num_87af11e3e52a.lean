-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_isMultiHomog_num_87af11e3e52a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:51.619492+00:00
-- url     : https://prove2.me/submissions/7f57dedd-b529-485b-8343-cd454c33f323

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_wh_form_35dda924265c
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
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
theorem _root_.solution [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) :
    IsMultiHomog (num g j a)
      (∑ k, ((a k).toNat • Function.extend Sum.inl (δ k) 0 + (-a k).toNat • Pi.single (Sum.inr k) 1)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((wh_form hg ⟨k, j k⟩).pow _).mul ((isWeightedHomogeneous_X ℤ _ _).pow _)
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
