-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.tensVd_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:12.93009+00:00
-- url     : https://prove2.me/submissions/e5cc458c-02de-4b10-9152-3831de909abd

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
    tensVd E a b f c = E a b (f c) - if c = b then f a else 0 := by
  simp only [tensVd, coordV, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]
end ReciprocityTheory.ChartRestriction.DS
