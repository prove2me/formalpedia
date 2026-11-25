-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layer_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:35.538208+00:00
-- url     : https://prove2.me/submissions/c5c4fe5b-f121-4337-a06f-744f70bf40e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB

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
variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {E' : Fin n → Fin n → Module.End ℂ M'}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) {V : Submodule ℂ M}
    {V' : Submodule ℂ M'} (hV : ∀ x ∈ V, f x ∈ V') :
    ∀ k, ∀ x ∈ layer ε E V k, f x ∈ layer ε E' V' k
  | 0 => hV
  | k + 1 => by
    have ih := solution f hf hV k
    have hle : layer ε E V (k + 1) ≤ (layer ε E' V' (k + 1)).comap f := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun x hx => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
      · exact (le_sup_left : layer ε E' V' k ≤ layer ε E' V' k ⊔ _) (ih x hx)
      · rintro _ ⟨x, hx, rfl⟩
        show f (E a b x) ∈ layer ε E' V' k ⊔ _
        rw [hf]
        refine (le_sup_right : _ ≤ layer ε E' V' k ⊔ _) ?_
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
          (Submodule.mem_iSup_of_mem hab ⟨f x, ih x hx, rfl⟩))
    exact fun x hx => hle hx
end ReciprocityTheory.ChartRestriction.DS
