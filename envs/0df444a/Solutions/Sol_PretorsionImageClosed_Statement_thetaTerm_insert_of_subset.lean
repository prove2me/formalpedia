-- Prove2me | solution 1 for PretorsionImageClosed.Statement.thetaTerm_insert_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:23:06.221354+00:00
-- url     : https://prove2.me/submissions/b6fb7e98-3033-440c-b39e-f4e22f690247

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
    thetaTerm (insert r R) J = thetaTerm R J * (if J = ∅ then X else 1) := by
  unfold thetaTerm admCount
  rw [Finset.filter_insert]
  by_cases hJe : J = ∅
  · subst hJe
    rw [if_pos (by simp), Finset.card_insert_of_notMem (fun h => lt_irrefl r (hr r (Finset.mem_filter.1 h).1))]
    simp only [if_true]
    ring
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJe
    rw [if_neg (fun h => not_lt.2 (h j hj) (hr j (hJ hj)))]
    simp only [if_neg hJe]
    ring
end PretorsionImageClosed.Statement
