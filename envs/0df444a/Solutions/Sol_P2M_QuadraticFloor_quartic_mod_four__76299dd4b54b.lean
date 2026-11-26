-- Prove2me | solution 1 for P2M_QuadraticFloor_quartic_mod_four__76299dd4b54b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:41.646264+00:00
-- url     : https://prove2.me/submissions/6e7ded4d-cb0a-4136-8e9a-34ee6e286b8f

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_P2M_QuadraticFloor_quartic_split__dd2adffe716c
public import Theorems.Thm_QuadraticFloor_floorSum_five_modEq

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ m : ℤ, (bern (40 * p) (Theta p)).re = m ∧ m ≡ 2 * (zB 1 p - zB 3 p) [ZMOD 4] := by
  refine ⟨floorSum 5 3 0 p - floorSum 5 1 0 p, (quartic_split' hp2 hp5).symm, ?_⟩
  have h3 := floorSum_five_modEq hp2 hp5 (B := 3) (by decide)
  have h1 := floorSum_five_modEq hp2 hp5 (B := 1) odd_one
  have := h3.sub h1
  rw [show floorSum 5 3 0 p - 1 - (floorSum 5 1 0 p - 1) = floorSum 5 3 0 p - floorSum 5 1 0 p by
    ring] at this
  refine this.trans ?_
  rw [show 2 * ((((p + 1) / 2 : ℕ) : ℤ) - zB 3 p) - 2 * ((((p + 1) / 2 : ℕ) : ℤ) - zB 1 p) =
    2 * (zB 1 p - zB 3 p) by ring]
end QuadraticFloor
