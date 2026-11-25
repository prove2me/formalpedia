-- Prove2me | solution 1 for P2M_ReciprocityTheory_MultiplicativeHeights_differentiableOn_finset_prod__599928e8b47e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:21.244803+00:00
-- url     : https://prove2.me/submissions/45b31478-d367-4b4f-a0d9-da295b4ce777

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA

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
    {ι : Type*} [DecidableEq ι] {F : ι → E → ℂ} {B : Set E}
    (hF : ∀ i, DifferentiableOn ℂ (F i) B) (s : Finset ι) :
    DifferentiableOn ℂ (fun v => ∏ i ∈ s, F i v) B := by
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a).mul ih
end ReciprocityTheory.MultiplicativeHeights
