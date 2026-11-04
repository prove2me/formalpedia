-- Prove2me | solution 1 for ThreeSum.Reporting.frontier_nodup_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:29.253192+00:00
-- url     : https://prove2.me/submissions/5f222602-fb08-4aa7-b733-ff4dca214e44

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting

set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]
namespace ThreeSum.Reporting
theorem _root_.solution (children : ℕ → List α) (query : ℕ → List α → ℕ)
    (hc : ∀ k, (children k).Nodup) (k : ℕ) : (frontier children query k).Nodup := by
  induction k with
  | zero => unfold frontier; split <;> simp
  | succ k ih =>
      apply List.Nodup.filter
      apply List.nodup_flatMap.mpr
      constructor
      · intro pre hpre
        apply (hc k).map
        intro x y hxy
        exact List.singleton_injective (List.append_cancel_left hxy)
      · apply ih.imp
        intro p q hpq
        apply List.disjoint_left.mpr
        intro t ht hq
        obtain ⟨x, hx, hxt⟩ := List.mem_map.mp ht
        obtain ⟨y, hy, hyt⟩ := List.mem_map.mp hq
        have heq : p ++ [x] = q ++ [y] := hxt.trans hyt.symm
        exact hpq (List.append_inj_left' heq (by rfl))
end ThreeSum.Reporting
