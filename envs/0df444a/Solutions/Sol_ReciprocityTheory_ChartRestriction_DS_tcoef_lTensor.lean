-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tcoef_lTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:55.903456+00:00
-- url     : https://prove2.me/submissions/f9953d24-4c76-4e59-baeb-2caf75c7b7d8

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
theorem _root_.solution (φ : Module.Dual ℂ (Fock n)) (S : Module.End ℂ (Fock n))
    (y : TensorProduct ℂ M (Fock n)) : tcoef φ (LinearMap.lTensor M S y) = tcoef (φ ∘ₗ S) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f => simp [tcoef_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end ReciprocityTheory.ChartRestriction.DS
