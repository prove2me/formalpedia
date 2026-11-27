-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.permute_mem_ncV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:41.513219+00:00
-- url     : https://prove2.me/submissions/178459c8-ea9b-4ad6-825e-0e08a91074c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_ncV_iff_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_permute_apply

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
theorem _root_.solution {k : ℕ} (σ : Equiv.Perm (Fin k)) {F : Big n k M} (hF : F ∈ ncV ε V k) :
    permute σ F ∈ ncV ε V k := by
  rw [mem_ncV_iff_apply] at hF ⊢
  intro κ
  rw [permute_apply]
  have hκ := hF (κ ∘ σ)
  by_cases hc : ∀ i, ε (κ i).1 ≠ ε (κ i).2
  · have hc' : ∀ i, ε ((κ ∘ σ) i).1 ≠ ε ((κ ∘ σ) i).2 := fun i => hc (σ i)
    rw [if_pos hc'] at hκ
    rw [if_pos hc]
    exact hκ
  · have hc' : ¬ ∀ i, ε ((κ ∘ σ) i).1 ≠ ε ((κ ∘ σ) i).2 := fun h => hc (fun i => by
      have := h (σ.symm i)
      simpa using this)
    rw [if_neg hc'] at hκ
    rw [if_neg hc]
    exact hκ
end ReciprocityTheory.ChartRestriction.DS
