-- Prove2me | solution 1 for QuadraticFloor.even_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:00.204803+00:00
-- url     : https://prove2.me/submissions/9379fa5a-9d9a-4ebe-a565-db43996b4dae

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution {A B : ℤ} (hAB : Even (A + B)) (n C : ℤ) : Even (A * n ^ 2 + B * n + C - C) := by
  rw [show A * n ^ 2 + B * n + C - C = n * (A * n + B) by ring]
  rcases Int.even_or_odd n with hn | ⟨m, rfl⟩
  · exact hn.mul_right _
  · apply Even.mul_left
    obtain ⟨r, hr⟩ := hAB
    exact ⟨A * m + r, by linear_combination hr⟩
end QuadraticFloor
