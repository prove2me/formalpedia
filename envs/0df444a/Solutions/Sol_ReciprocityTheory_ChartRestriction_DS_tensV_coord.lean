-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tensV_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:03.435883+00:00
-- url     : https://prove2.me/submissions/f48e60f4-228c-42cd-b66b-bc5a546a289a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + if c = a then f b else 0 := by
  simp only [tensV, coordV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]
end ReciprocityTheory.ChartRestriction.DS
