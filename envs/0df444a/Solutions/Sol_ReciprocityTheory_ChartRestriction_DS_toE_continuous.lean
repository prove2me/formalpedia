-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.toE_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:08.224811+00:00
-- url     : https://prove2.me/submissions/185d9a7e-955b-47f1-9f68-a985dca0a180

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (n : ℕ) : Continuous (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) := by

  let f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EH n →L[ℂ] EH n) :=
    { toFun := toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      map_add' := map_add _
      map_smul' := map_smul _ }
  exact f.continuous_of_finiteDimensional
end ReciprocityTheory.ChartRestriction.DS
