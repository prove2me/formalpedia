-- Prove2me | solution 1 for QuadraticFloor.sum_modEq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:23.612582+00:00
-- url     : https://prove2.me/submissions/92beafa4-2c98-4898-98f1-915a7ed125af

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
namespace QuadraticFloor
theorem _root_.solution {s : Finset ℕ} {f : ℕ → ℤ} (hf : ∀ j ∈ s, f j = 0 ∨ f j = 1 ∨ f j = -1) :
    ∑ j ∈ s, f j ≡ (s.filter fun j => f j ≠ 0).card [ZMOD 2] := by
  rw [card_filter]
  push_cast
  apply Int.ModEq.sum
  intro j hj
  rcases hf j hj with h | h | h <;> simp [h] <;> decide
end QuadraticFloor
