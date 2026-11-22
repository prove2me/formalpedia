-- Prove2me | solution 1 for Stable.eq_hist_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:45:39.231824+00:00
-- url     : https://prove2.me/submissions/d87b79cd-53c0-4235-940b-7eaca367cc04

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_Prime_top_mem
import Theorems.Thm_Stable_Prime_eq_hist_top
import Theorems.Thm_Stable_hist_config
import Theorems.Thm_Stable_hist_least
import Theorems.Thm_Stable_hist_mem


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {p : Prime F} (hp : p.val ⊆ c) : p.val = hist F c (Prime.top p) := by
  have htc : Prime.top p ∈ c := hp (Prime.top_mem p)
  refine Set.Subset.antisymm ?_ (hist_least p.config hp (Prime.top_mem p))
  refine (Prime.eq_hist_top p).trans_subset
    (hist_least (hist_config hF hc htc) ?_ hist_mem)
  exact hist_least p.config hp (Prime.top_mem p)
end Stable
