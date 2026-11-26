-- Prove2me | solution 1 for P2M_QuadraticFloor_quadratic_half__fa71830266b8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:13.043414+00:00
-- url     : https://prove2.me/submissions/17593a4f-3002-4296-aa49-a94cf6007535

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_xi_two
public import Theorems.Thm_QuadraticFloor_one_two
public import Theorems.Thm_QuadraticFloor_xixi_two
public import Theorems.Thm_QuadraticFloor_starxi_two
public import Theorems.Thm_QuadraticFloor_sum_char5
public import Theorems.Thm_QuadraticFloor_three_sq
public import Theorems.Thm_QuadraticFloor_vartheta_one
public import Theorems.Thm_QuadraticFloor_vartheta_xixi
public import Theorems.Thm_QuadraticFloor_admissible_five_one
public import Theorems.Thm_QuadraticFloor_admissible_five_three
public import Theorems.Thm_QuadraticFloor_floorSum_five

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((floorSum 5 1 0 p + floorSum 5 3 0 p - 2 : ℤ) : ℂ) = -(1 / 2) *
      (bern (40 * p) (fun x => (eta p x : ℂ) * (if 5 ∣ x then 0 else 1)) +
        bern (40 * p) (fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ))) := by
  have h3 := floorSum_five hp2 hp5 admissible_five_three
  have h1 := floorSum_five hp2 hp5 admissible_five_one
  rw [sum_char5] at h3 h1
  simp only [Int.cast_one, one_pow, map_one, one_mul] at h1
  rw [three_sq] at h3
  simp only [map_pow, one_two, xi_two, xixi_two, starxi_two, map_one, one_pow, Complex.I_sq,
    neg_sq, map_neg] at h3
  rw [vartheta_one, vartheta_xixi] at h3 h1
  push_cast
  rw [h3, h1]
  ring
end QuadraticFloor
