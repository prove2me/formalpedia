-- Prove2me | solution 1 for P2M_BooleanIsoperimetry_HIncrement_eq_min__d487d18fa7b9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:03.453012+00:00
-- url     : https://prove2.me/submissions/02b56a1b-9940-4168-8281-7270b440aa01

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
public import Theorems.Thm_BooleanIsoperimetry_HIncrement_eq_gShift_inv
public import Theorems.Thm_BooleanIsoperimetry_gShift_preimage_eq_insert_below_min
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (p : ℕ) (w : Cube n) (hw : rank w = p) (hne : w.Nonempty) :
    HIncrement n p = (w.min' hne : ℕ) := by
  have hinj : Set.InjOn (fun j : Fin n => insert j w)
      (↑(Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ)))) := by
    intro j hj j' hj' hjj'
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
    have hjw : j ∉ w := fun hc => by have := Finset.min'_le w j hc; omega
    simp only at hjj'
    have : j ∈ insert j' w := hjj' ▸ Finset.mem_insert_self j w
    rcases Finset.mem_insert.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hjw
  rw [HIncrement_eq_gShift_inv n p w hw, gShift_preimage_eq_insert_below_min w hne,
      Finset.card_image_of_injOn hinj]
  have himg : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ))).image (Fin.val)
      = Finset.range (w.min' hne : ℕ) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hk; exact ⟨⟨k, by have := (w.min' hne).2; omega⟩, hk, rfl⟩
  calc (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ))).card
      = ((Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ))).image (Fin.val)).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = (Finset.range (w.min' hne : ℕ)).card := by rw [himg]
    _ = (w.min' hne : ℕ) := Finset.card_range _
end BooleanIsoperimetry
