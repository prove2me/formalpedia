-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_diffOn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:10:45.504622+00:00
-- url     : https://prove2.me/submissions/434ee50e-b634-4aab-86cf-dd6186010d57

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.L2DbarEstimates.Y.fn_hom_zero

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} (De : MvPolynomial (Fin n) ℂ)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (u : Finset (Fin n)) (f : Fin n → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (f k) S) :
    DifferentiableOn ℂ (fun x => ∏ k ∈ u, f k x) S := by
  first
    | exact DifferentiableOn.finset_prod (fun k _ => h k)
    | exact DifferentiableOn.fun_finset_prod (fun k _ => h k)
    | (classical
       induction u using Finset.induction_on with
       | empty => simp [differentiableOn_const]
       | insert k u hk ih =>
         simp only [Finset.prod_insert hk]
         exact (h _).mul ih)
end ReciprocityTheory.L2DbarEstimates.Y
