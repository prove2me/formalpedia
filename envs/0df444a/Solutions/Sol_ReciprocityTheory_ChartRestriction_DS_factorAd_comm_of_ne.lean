-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.factorAd_comm_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:25.903241+00:00
-- url     : https://prove2.me/submissions/7ebdeb6e-54a2-4860-9f76-cde5cd47cfdd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply

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
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
variable {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) {i j : Fin k} (hij : i ≠ j) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k j c d = factorAd k j c d * factorAd k i a b := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  simp only [Module.End.mul_apply, factorAd_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Function.update_comm hij.symm]
  split_ifs <;> abel
end ReciprocityTheory.ChartRestriction.DS
