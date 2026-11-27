-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.physSub_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:58.008955+00:00
-- url     : https://prove2.me/submissions/dac0745a-ce9b-4d6f-b7c7-f2052a4bb58a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_physicalSubspace_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gradT_cmT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_cpT_cmT_isCAR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eT_commutesCAR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fockT_stable_gen


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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, eT E a b x ∈ physicalSubspace ε) ∧
      (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, diagE ε (eT E) cpT cmT a b x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp ε (eT E) cpT x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp' ε (eT E) cmT x ∈ physicalSubspace ε) ∧
      ∀ x ∈ physicalSubspace (N := N) ε, gradT x ∈ physicalSubspace ε := by
  have hC := cpT_cmT_isCAR (N := N) (n := n)
  have hK := eT_commutesCAR (N := N) E
  refine ⟨fun a c x hx => ?_, fun a c x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rw [mem_physicalSubspace_iff] at hx ⊢ <;> intro j b hjb
  · exact (fockT_stable_gen hC hK ε hjb hx).1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.1
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.2
  · have h := LinearMap.congr_fun (gradT_cmT (N := N) j b) x
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
    rw [← neg_neg (cmT j b (gradT x)), ← h, hx j b hjb, map_zero, neg_zero]
end ReciprocityTheory.ChartRestriction.DS
