-- Prove2me | solution 1 for PretorsionImageClosed.Statement.thetaTerm_insert_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:23:06.85399+00:00
-- url     : https://prove2.me/submissions/25ccbb05-28ae-4958-91f6-5aee83e94d35

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {r : ι} {R J : Finset ι} (hr : ∀ x ∈ R, x < r) (hJ : J ⊆ R) :
    thetaTerm (insert r R) (insert r J) = C q * X * thetaTerm R J := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  have hrJ : r ∉ J := fun h => hrR (hJ h)
  unfold thetaTerm admCount
  have hne : insert r J ≠ ∅ := Finset.insert_ne_empty _ _
  rw [if_neg hne, Finset.card_insert_of_notMem hrJ, Finset.filter_insert]
  have hfilter : R.filter (fun c => ∀ j ∈ insert r J, c ≤ j) = R.filter (fun c => ∀ j ∈ J, c ≤ j) := by
    apply Finset.filter_congr
    intro c hc
    constructor
    · intro h j hj
      exact h j (Finset.mem_insert_of_mem hj)
    · intro h j hj
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · exact (hr c hc).le
      · exact h j hj'
  rw [hfilter]
  by_cases hJe : J = ∅
  · subst hJe
    rw [if_pos (by simp), Finset.card_insert_of_notMem (fun h => hrR (Finset.mem_filter.1 h).1)]
    simp only [if_true, Finset.card_empty, pow_zero, map_one, pow_succ, map_mul]
    ring
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJe
    rw [if_neg (fun h => not_lt.2 (h j (Finset.mem_insert_of_mem hj)) (hr j (hJ hj))), if_neg hJe]
    simp only [pow_succ, map_mul]
    ring
end PretorsionImageClosed.Statement
