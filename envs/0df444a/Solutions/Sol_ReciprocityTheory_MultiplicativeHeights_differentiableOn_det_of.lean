-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:53.87901+00:00
-- url     : https://prove2.me/submissions/bf88e71f-e1c3-4e52-8fd8-b8f157bd1f78

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Theorems.Thm_P2M_ReciprocityTheory_MultiplicativeHeights_differentiableOn_finset_prod__599928e8b47e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix Filter Topology Set
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Type} [Fintype U] [DecidableEq U] {F : U → U → E → ℂ} {B : Set E}
    (hF : ∀ a b, DifferentiableOn ℂ (F a b) B) :
    DifferentiableOn ℂ (fun v => (Matrix.of fun a b => F a b v).det) B := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  exact (differentiableOn_const _).mul
    (differentiableOn_finset_prod' (F := fun i v => F (σ i) i v) (fun i => hF _ _) _)
end ReciprocityTheory.MultiplicativeHeights
