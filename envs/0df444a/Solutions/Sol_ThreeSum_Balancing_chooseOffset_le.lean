-- Prove2me | solution 1 for ThreeSum.Balancing.chooseOffset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:49.379188+00:00
-- url     : https://prove2.me/submissions/1f9014b3-a577-4dff-9a37-1c224a148ccc

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_Balancing

set_option autoImplicit false
open ThreeSum ThreeSum.Balancing
open Finset
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]
namespace ThreeSum.Balancing
theorem _root_.solution [Inhabited G] (keys : List G) (F H : G → ℕ)
    {d : G} (hd : d ∈ keys) :
    correlation F H (chooseOffset keys F H) ≤ correlation F H d := by
  unfold chooseOffset
  cases h : keys.argmin (correlation F H) with
  | none => have := List.argmin_eq_none.mp h; simp_all
  | some v =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmin (f := correlation F H) hd
      (by simpa only [Option.mem_def] using h)
end ThreeSum.Balancing
