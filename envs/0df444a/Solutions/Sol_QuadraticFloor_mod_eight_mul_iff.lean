-- Prove2me | solution 1 for QuadraticFloor.mod_eight_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:04.8024+00:00
-- url     : https://prove2.me/submissions/4dc40b23-cb9a-4b7d-92a9-0308a8507537

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {A x d : ℕ} (hA : Odd A) (hd : d < 8 * A) :
    x % (8 * A) = d ↔ x % 8 = d % 8 ∧ x % A = d % A := by
  have hc : Nat.Coprime 8 A := by
    have := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 hA); simpa using this
  have : x % (8 * A) = d ↔ x ≡ d [MOD 8 * A] := by
    unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hd]
  rw [this, ← Nat.modEq_and_modEq_iff_modEq_mul hc]
  rfl
end QuadraticFloor
