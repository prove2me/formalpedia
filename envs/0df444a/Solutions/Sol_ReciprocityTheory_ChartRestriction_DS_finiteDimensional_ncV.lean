-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.finiteDimensional_ncV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:26.676659+00:00
-- url     : https://prove2.me/submissions/181520fe-7e73-4707-a7bc-c951142c1d63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_big_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_mem

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hV : FiniteDimensional ℂ V) (k : ℕ) :
    FiniteDimensional ℂ (ncV ε V k) := by
  haveI := hV
  let f : ncV ε V k →ₗ[ℂ] ((Fin k → Fin n × Fin n) → V) :=
    LinearMap.pi fun κ => LinearMap.codRestrict V ((coord k κ).comp (ncV ε V k).subtype)
      (fun F => ncV_mem F.2 κ)
  refine FiniteDimensional.of_injective f ?_
  intro F G h
  apply Subtype.ext
  apply big_ext
  intro κ
  exact congrArg Subtype.val (congrFun h κ)
end ReciprocityTheory.ChartRestriction.DS
