-- Prove2me | solution 1 for P2M_BooleanIsoperimetry_cube_min__add_card_le_534aca28a63b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:02.729463+00:00
-- url     : https://prove2.me/submissions/e5b4fca1-8575-4551-950e-d8863806667b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    (w.min' h : ℕ) + w.card ≤ n := by
  have hsub : w ⊆ Finset.Ici (w.min' h) := fun x hx =>
    Finset.mem_Ici.mpr (Finset.min'_le w x hx)
  have hcard : w.card ≤ (Finset.Ici (w.min' h)).card := Finset.card_le_card hsub
  have hIci : (Finset.Ici (w.min' h)).card = n - (w.min' h : ℕ) := by simp [Fin.card_Ici]
  omega
end BooleanIsoperimetry
