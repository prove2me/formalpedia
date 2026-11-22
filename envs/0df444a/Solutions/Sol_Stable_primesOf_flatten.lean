-- Prove2me | solution 1 for Stable.primesOf_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:15:25.817323+00:00
-- url     : https://prove2.me/submissions/7193f45c-a7a3-40c2-92e5-db3eccd96212

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_Prime_top_mem
import Theorems.Thm_Stable_subset_flatten
import Theorems.Thm_Stable_eq_hist_of_subset
import Theorems.Thm_Stable_hist_least


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) {S : Set (Prime F)}
    (hS : isConf (toPES F) S) (hflat : F.Config (flatten F S)) :
    primesOf F (flatten F S) = S := by
  refine Set.Subset.antisymm (fun p hp => ?_) (fun p hp => subset_flatten hp)
  obtain ⟨-, ⟨q, rfl⟩, -, ⟨hq, rfl⟩, htq⟩ := hp (Prime.top_mem p)
  refine hS.2 hq (show p.val ⊆ q.val from ?_)
  rw [eq_hist_of_subset hF hflat hp]
  exact hist_least q.config (subset_flatten hq) htq
end Stable
