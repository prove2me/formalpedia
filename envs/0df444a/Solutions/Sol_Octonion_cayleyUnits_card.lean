-- Prove2me | solution 1 for Octonion.cayleyUnits_card
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:54.953958+00:00
-- url     : https://prove2.me/submissions/f3c51bdc-cb48-4de9-9ac2-81b0110d0309

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_cayleyUnits
import Definitions.Def_Octonion_octonions
import Definitions.Def_Octonion_toRat8
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Octonion

/-- Doubling the coordinates loses no information. -/
private theorem halfOf_injective : Function.Injective halfOf := by
  intro a b h
  funext i
  have hi := congrArg (fun x => coord8 x i) h
  simp only [coord8_halfOf] at hi
  have : (a i : ℚ) = b i := (div_left_inj' (by norm_num : (2 : ℚ) ≠ 0)).mp hi
  exact_mod_cast this

private theorem halfOf_neg (a : Fin 8 → ℤ) : halfOf (-a) = -halfOf a := by
  apply ext_coord8
  intro i
  simp [coord8_halfOf, coord8_neg, neg_div]

/-- Doubled coordinates of the enumerated units. Counting integer vectors avoids
repeated rational arithmetic when the kernel deduplicates the enumeration. -/
private def unitNumerators : Finset (Fin 8 → ℤ) :=
  ((Finset.univ : Finset (Fin 8)).biUnion fun k =>
    {fun i => if i = k then 2 else 0, -(fun i => if i = k then 2 else 0)}) ∪
  weight4Masks.biUnion fun m => (Finset.range 256).image
    (fun t i => if Nat.testBit m i.val then if Nat.testBit t i.val then 1 else -1 else 0)

private theorem cayleyUnits_eq_image : cayleyUnits = unitNumerators.image halfOf := by
  simp only [unitNumerators, Finset.image_union, Finset.biUnion_image,
    Finset.image_insert, Finset.image_singleton, halfOf_neg, Finset.image_image]
  rfl

/-- Product equality short-circuits coordinate comparisons during the finite count. -/
private def integerTuple (a : Fin 8 → ℤ) : (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) :=
  ((a 0, a 1, a 2, a 3), (a 4, a 5, a 6, a 7))

private theorem integerTuple_injective : Function.Injective integerTuple := by
  intro a b h
  simp only [integerTuple, Prod.mk.injEq] at h
  funext i
  fin_cases i <;> simp_all

end Octonion

open Octonion

/-- The Cayley integers have 240 units. The finite count is checked by the kernel
on doubled integer coordinates and transported through the injective map `halfOf`. -/
theorem solution : Octonion.cayleyUnits.card = 240 := by
  rw [cayleyUnits_eq_image, Finset.card_image_of_injective _ halfOf_injective]
  rw [← Finset.card_image_of_injective unitNumerators integerTuple_injective]
  simp only [unitNumerators, Finset.image_union, Finset.biUnion_image,
    Finset.image_insert, Finset.image_singleton, Finset.image_image]
  decide +kernel

namespace Octonion


end Octonion
