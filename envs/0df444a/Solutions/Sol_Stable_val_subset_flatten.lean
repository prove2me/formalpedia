-- Prove2me | solution 1 for Stable.val_subset_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:04:06.047466+00:00
-- url     : https://prove2.me/submissions/dfeedcfb-558d-46d4-9707-6086f2ff957b

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_subset_flatten
import Theorems.Thm_Stable_histPrime_lt
import Theorems.Thm_Stable_hist_mem


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) (hcf : CoincidenceFree F)
    {c : Set (Prime F)} {p : Prime F} (hpast : ∀ q : Prime F, q < p → q ∈ c) :
    p.val ⊆ flatten F c ∪ {Prime.top p} := by
  intro t ht
  by_cases hne : t = Prime.top p
  · exact Or.inr hne
  · exact Or.inl (subset_flatten (hpast _ (histPrime_lt hF hcf p ht hne)) hist_mem)
end Stable
