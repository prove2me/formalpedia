-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTransport.choices_map_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:06.75819+00:00
-- url     : https://prove2.me/submissions/7ee7d251-31df-4cad-a8aa-1f5b0c91140d

import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Theorems.Thm_ThreeSum_BooleanGreedy_state_subset
import Theorems.Thm_ThreeSum_IndexedGreedy_argmax_map
import Definitions.Def_WeightedCache3SUM_Alias_016e82cb2808b14f


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTransport
open Finset
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]
namespace ThreeSum.LightLocalCoverTransport
theorem _root_.solution
    (matrix : ℕ → ℕ → ℕ) (candidate : ℕ → Ω) (target : ℕ → U)
    (covers : Ω → U → Prop) [DecidableRel covers]
    {rows cols : ℕ} (hrows : 0 < rows)
    (hinj : Set.InjOn target (range cols))
    (hcover : ∀ i, ∀ j < cols, BooleanGreedy.covers matrix i j ↔ covers (candidate i) (target j))
    (rounds : ℕ) :
    (BooleanGreedy.choices matrix rows cols rounds).map candidate =
      Cover.greedyChoices ((List.range rows).map candidate) covers
        ((range cols).image target) rounds := by
  have hscore (old : Finset ℕ) (hold : old ⊆ range cols) (i : ℕ) :
      ((old.image target).filter (covers (candidate i))).card =
        (old.filter (BooleanGreedy.covers matrix i)).card := by
    rw [filter_image]
    have hfilter : (old.filter fun j => covers (candidate i) (target j)) =
        old.filter (BooleanGreedy.covers matrix i) := by
      apply filter_congr
      intro j hj
      exact (hcover i j (mem_range.mp (hold hj))).symm
    rw [hfilter]
    apply card_image_of_injOn
    intro a ha b hb he
    exact hinj (hold (mem_filter.mp ha).1) (hold (mem_filter.mp hb).1) he
  have hselect (old : Finset ℕ) (hold : old ⊆ range cols) :
      Cover.selectMap ((List.range rows).map candidate) covers (old.image target) =
        candidate (Cover.selectMap (List.range rows) (BooleanGreedy.covers matrix) old) := by
    unfold Cover.selectMap
    rw [IndexedGreedy.argmax_map]
    have hf : (fun x => ((old.image target).filter (covers x)).card) ∘ candidate =
        (fun i => (old.filter (BooleanGreedy.covers matrix i)).card) := by
      funext i
      exact hscore old hold i
    rw [hf,IndexedGreedy.argmax_range _ hrows]
    rfl
  have hstates : ∀ t,
      (BooleanGreedy.state matrix rows cols t).image target =
        Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change ((BooleanGreedy.state matrix rows cols t).filter
          (fun j => ¬BooleanGreedy.covers matrix (BooleanGreedy.choice matrix rows cols t) j)).image target =
        (Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t).filter
          (fun u => ¬covers (Cover.selectMap ((List.range rows).map candidate) covers
            (Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t)) u)
      rw [← ih,hselect _ (BooleanGreedy.state_subset matrix rows cols t),filter_image]
      apply congrArg (Finset.image target)
      apply filter_congr
      intro j hj
      exact not_congr (hcover _ j (mem_range.mp (BooleanGreedy.state_subset matrix rows cols t hj)))
  induction rounds with
  | zero => rfl
  | succ t ih =>
    change (BooleanGreedy.choices matrix rows cols t ++ [BooleanGreedy.choice matrix rows cols t]).map candidate =
      Cover.greedyChoices ((List.range rows).map candidate) covers ((range cols).image target) t ++
        [Cover.selectMap ((List.range rows).map candidate) covers
          (Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t)]
    rw [List.map_append,List.map_singleton,ih,← hstates t,
      hselect _ (BooleanGreedy.state_subset matrix rows cols t)]
    rfl
end ThreeSum.LightLocalCoverTransport
