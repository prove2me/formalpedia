-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_diffOn_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:22:26.875913+00:00
-- url     : https://prove2.me/submissions/3b2e70f1-5831-450a-beec-02b287780c6a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ImportsAlt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_hom_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_diffOn_prod
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
    {a : E → ℂ} {b : Fin n → E → ℂ} (ha : DifferentiableOn ℂ a S)
    (hb : ∀ k, DifferentiableOn ℂ (b k) S) :
    DifferentiableOn ℂ (fun x => fnHom De (a x) (fun k => b k x)) S := by
  unfold fnHom
  have hterm : ∀ m ∈ De.support, DifferentiableOn ℂ (fun x => MvPolynomial.coeff m De *
      (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k)) S := fun m _ =>
    ((ha.pow _).mul (fn_diffOn_prod Finset.univ (fun k x => b k x ^ m k) (fun k => (hb k).pow _))).const_mul _
  first
    | exact DifferentiableOn.fun_sum hterm
    | exact DifferentiableOn.sum hterm
    | (have e : (fun x => ∑ m ∈ De.support, MvPolynomial.coeff m De *
          (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k)) =
          ∑ m ∈ De.support, fun x => MvPolynomial.coeff m De *
          (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k) := by
         ext x; simp [Finset.sum_apply]
       rw [e]
       exact DifferentiableOn.sum hterm)
end ReciprocityTheory.L2DbarEstimates.Y
