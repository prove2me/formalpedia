-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.hasGelfandChar_span_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:47.42001+00:00
-- url     : https://prove2.me/submissions/8b2f3c97-865e-4a35-9ea1-ad74b80c6e74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_infinitesimalShift_reversed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_antiE_hw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_antiE_isGlRep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gelfand_hw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gval_perm


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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) : HasGelfandChar E (ν + rho n) (Submodule.span ℂ {v}) := by
  intro k x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨?_, ?_⟩
  · rw [map_smul, gelfand_hw hE hv k, smul_comm]
  · rw [map_smul, gelfand_hw (antiE_isGlRep hE) (antiE_hw hv) k, infinitesimalShift_reversed, gval_perm, smul_comm]
end ReciprocityTheory.ChartRestriction.DS
