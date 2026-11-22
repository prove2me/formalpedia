-- Prove2me | solution 1 for Stable.flatten_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:15:47.2568+00:00
-- url     : https://prove2.me/submissions/1917282c-7003-434b-b27a-9edd44619b85

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_Prime_top_mem
import Theorems.Thm_Stable_subset_flatten
import Theorems.Thm_Stable_val_subset_flatten

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) (hcf : CoincidenceFree F)
    {c : Set (Prime F)} {p : Prime F} (hpast : ∀ q : Prime F, q < p → q ∈ c) :
    flatten F (c ∪ {p}) = flatten F c ∪ {Prime.top p} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨-, ⟨q, rfl⟩, -, ⟨hq | hq, rfl⟩, hxq⟩
    · exact Or.inl (subset_flatten hq hxq)
    · exact val_subset_flatten hF hcf hpast ((Set.mem_singleton_iff.mp hq) ▸ hxq)
  · rintro x (hx | hx)
    · obtain ⟨-, ⟨q, rfl⟩, -, ⟨hq, rfl⟩, hxq⟩ := hx
      exact subset_flatten (Or.inl hq) hxq
    · exact subset_flatten (Or.inr rfl) ((Set.mem_singleton_iff.mp hx) ▸ Prime.top_mem p)
end Stable
