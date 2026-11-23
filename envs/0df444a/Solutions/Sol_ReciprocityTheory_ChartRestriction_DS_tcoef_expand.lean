-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tcoef_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:58.138346+00:00
-- url     : https://prove2.me/submissions/5bb6ded1-101b-47e4-b84f-ec6901c095b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tcoef_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (y : TensorProduct ℂ M (Fock n)) :
    y = ∑ s, tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f =>
    simp only [tcoef_tmul, Module.Basis.coord_apply, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, (fockBasis n).sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
end ReciprocityTheory.ChartRestriction.DS
