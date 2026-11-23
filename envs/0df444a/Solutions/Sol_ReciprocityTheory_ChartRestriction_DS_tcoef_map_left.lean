-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tcoef_map_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:10.466294+00:00
-- url     : https://prove2.me/submissions/3e77cc28-d708-4b83-adfc-a30a831c05bf

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
theorem _root_.solution {M' : Type*} [AddCommGroup M'] [Module ℂ M'] (φ : Module.Dual ℂ (Fock n))
    (T : M' →ₗ[ℂ] M) (y : TensorProduct ℂ M' (Fock n)) :
    tcoef φ (TensorProduct.map T LinearMap.id y) = T (tcoef φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m f => simp [tcoef_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end ReciprocityTheory.ChartRestriction.DS
