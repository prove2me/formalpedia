-- Prove2me | solution 1 for Stable.Prime.eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:45:35.485573+00:00
-- url     : https://prove2.me/submissions/a4793f4b-ae67-4aca-9ada-dac2f49d667f

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_Prime_top_mem
import Theorems.Thm_Stable_Prime_eq_hist_top
import Theorems.Thm_Stable_hist_least


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime
namespace Stable.Prime
theorem _root_.solution (hcf : CoincidenceFree F) (p : Prime F) {y : F.Event}
    (hy : y ∈ p.val) (hh : p.val = hist F p.val y) : y = top p := by
  by_contra hne
  obtain ⟨m, hm, hmp, hiff⟩ := hcf p.config hy (top_mem p) hne
  by_cases hym : y ∈ m
  · exact (hiff.mp hym) (Set.Subset.antisymm hmp (hh ▸ hist_least hm hmp hym) ▸ top_mem p)
  · have htm : top p ∈ m := not_not.mp fun h => hym (hiff.mpr h)
    exact hym (Set.Subset.antisymm hmp ((eq_hist_top p) ▸ hist_least hm hmp htm) ▸ hy)
end Stable.Prime
