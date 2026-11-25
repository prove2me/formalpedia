-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.layer_le_genSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:49.75652+00:00
-- url     : https://prove2.me/submissions/303c3615-a321-4d55-86b0-5f4879418765

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_of_stable

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
theorem _root_.solution (k : ℕ) : layer ε E V k ≤ genSub E V := by
  refine layer_le_of_stable (le_sInf fun T hT => hT.1) ?_ k
  intro a b v hv
  simp only [genSub, Submodule.mem_sInf, Set.mem_setOf_eq] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)
end ReciprocityTheory.ChartRestriction.DS
