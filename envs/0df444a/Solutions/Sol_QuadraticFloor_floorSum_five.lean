-- Prove2me | solution 1 for QuadraticFloor.floorSum_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:52.050364+00:00
-- url     : https://prove2.me/submissions/6e4d5e53-d21a-46d9-ad1d-af709126b5ae

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_weight
public import Theorems.Thm_P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) {B : ℤ} (hB : Admissible 5 B 0) :
    (floorSum 5 B 0 p : ℂ) = 1 - (1 / 4) *
      ∑ ψ : DirichletCharacter ℂ 5,
        starRingEnd ℂ (ψ ((B : ZMod 5) ^ 2)) * bern (40 * p) (vartheta p ψ) := by
  have hpA : ¬ p ∣ 5 := fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).1 h)
  have h := square_class_decomposition' (A := 5) hp2 (by decide) hpA hB
  push_cast at h
  rw [h, show Nat.totient 5 = 4 by decide, show 8 * 5 * p = 40 * p by ring]
  simp only [Int.negOnePow_zero, Units.val_one, Int.cast_one, Nat.cast_ofNat, weight]
end QuadraticFloor
