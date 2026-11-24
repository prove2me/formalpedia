-- Prove2me | solution 1 for aux_lem_flt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:22.621805+00:00
-- url     : https://prove2.me/submissions/8fbdf1af-91e2-450f-a791-4f622852d0f1

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat

set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional Polynomial Algebra Nat Finset Fintype
variable (p : ℕ) (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
open scoped NumberField
open Ideal IsCyclotomicExtension
local notation "R" => 𝓞 (CyclotomicField p ℚ)
variable {p}
open IsPrimitiveRoot
theorem _root_.solution [Fact p.Prime] {x y z : ℤ} (H : x ^ p + y ^ p = z ^ p)
    (caseI : ¬↑p ∣ x * y * z) : ¬(p : ℤ) ∣ (x + y : ℤ) := by
  intro habs
  replace habs : ↑p ∣ (x + y : ℤ) := by simpa using habs
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add] at habs
  replace H := congr_arg (fun x : ℤ ↦ (x : ZMod p)) H.symm
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card, habs,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at H
  exact caseI (Dvd.dvd.mul_left H _)
