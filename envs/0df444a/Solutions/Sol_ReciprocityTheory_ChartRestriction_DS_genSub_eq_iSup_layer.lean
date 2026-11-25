-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.genSub_eq_iSup_layer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:37.471648+00:00
-- url     : https://prove2.me/submissions/3004ebe1-60f2-4552-8ef1-e88ae5e47112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_genSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_layer_succ

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V) :
    genSub E V = ⨆ k, layer ε E V k := by
  have hmono : Monotone (layer ε E V) := monotone_nat_of_le_succ fun k => layer_le_succ k
  refine le_antisymm (sInf_le ⟨le_iSup_of_le 0 le_rfl, fun a b v hv => ?_⟩) (iSup_le layer_le_genSub)
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hv
  exact (le_iSup (layer ε E V) (k + 1)) (apply_mem_layer_succ hE hV a b hk)
end ReciprocityTheory.ChartRestriction.DS
