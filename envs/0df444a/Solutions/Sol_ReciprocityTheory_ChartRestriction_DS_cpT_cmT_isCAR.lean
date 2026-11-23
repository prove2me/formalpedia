-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.cpT_cmT_isCAR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:20.505484+00:00
-- url     : https://prove2.me/submissions/92eb93a4-eebd-41b8-a850-d7c4ac8bc148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isCAR_fock


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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution : IsCAR (cpT (N := N) (n := n)) cmT := by
  intro i a j b
  obtain ⟨h1, h2, h3⟩ := isCAR_fock (n := n) i a j b
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h1
    simp only [map_add, map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h2
    simp only [map_add, map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h3
    rw [map_add, map_mul, map_mul] at h
    refine h.trans ?_
    split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS
