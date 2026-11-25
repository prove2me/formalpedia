-- Prove2me | solution 1 for SCCThm8.cntLift_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:09.497209+00:00
-- url     : https://prove2.me/submissions/dfc0f9e0-cf50-44f6-9992-c1ca074de15c

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
public import Theorems.Thm_SCCThm8_cntLift_bounds
public import Theorems.Thm_SCCThm8_cntLift_eq_one
public import Theorems.Thm_SCCThm8_cntLift_eq_neg_one
public import Theorems.Thm_SCCThm8_cntRank_mono

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} (v v' : Finset (Fin n)) :
    (∀ i, -1 ≤ cntLift v i - cntLift v' i) ∨ (∀ i, -1 ≤ cntLift v' i - cntLift v i) := by
  by_contra hcon
  simp only [not_or, not_forall, not_le] at hcon
  obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := hcon
  have bj := cntLift_bounds v j
  have bj' := cntLift_bounds v' j
  have bi := cntLift_bounds v i
  have bi' := cntLift_bounds v' i
  obtain ⟨-, hvj2⟩ := cntLift_eq_neg_one (v := v) (i := j) (by omega)
  obtain ⟨-, hv'j2⟩ := cntLift_eq_one (v := v') (i := j) (by omega)
  obtain ⟨-, hvi2⟩ := cntLift_eq_one (v := v) (i := i) (by omega)
  obtain ⟨-, hv'i2⟩ := cntLift_eq_neg_one (v := v') (i := i) (by omega)
  rcases lt_trichotomy i j with hij | rfl | hji
  · have := cntRank_mono v' hij
    omega
  · omega
  · have := cntRank_mono v hji
    omega
end SCCThm8
