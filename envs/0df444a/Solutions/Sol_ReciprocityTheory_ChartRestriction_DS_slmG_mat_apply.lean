-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slmG_mat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:41.753919+00:00
-- url     : https://prove2.me/submissions/cb112d51-f1ee-4da7-8006-d2a2b5ebd956

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmG_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slmEnt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_re_mul_add_im_mul_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (q : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → Fin n → E) (W : Matrix (Fin n) (Fin n) ℂ) :
    slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) (fun i => slmc m i q • v i.1 i.2.1) W =
      ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • v a b := by
  refine (slmG_apply (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) _ W).trans ?_
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slmC, slmc, ↓reduceIte, Bool.false_eq_true,
    ContinuousLinearMap.coe_comp', Function.comp_apply, slmEnt_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Matrix.mul_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [← re_mul_add_im_mul_I (fderiv ℝ γ q W k b) (m q a k)]
  simp only [add_smul, mul_smul, Complex.coe_smul]
  rfl
end ReciprocityTheory.ChartRestriction.DS
