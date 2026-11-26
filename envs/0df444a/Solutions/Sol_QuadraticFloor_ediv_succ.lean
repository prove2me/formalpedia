-- Prove2me | solution 1 for QuadraticFloor.ediv_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:30.720324+00:00
-- url     : https://prove2.me/submissions/c5d730cf-9c83-45f3-a8bd-3ceef191399f

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_ite_of_neg
public import Theorems.Thm_QuadraticFloor_ite_of_pos


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution (hp0 : 0 < (p : ℤ)) (v : ℤ) :
    (v + 1) / (p : ℤ) = v / p + if (p : ℤ) ∣ v + 1 then 1 else 0 := by
  have hv := Int.emod_add_mul_ediv v p
  have hr0 := Int.emod_nonneg v hp0.ne'
  have hrp := Int.emod_lt_of_pos v hp0
  set q := v / (p : ℤ)
  set r := v % (p : ℤ)
  by_cases hr : r + 1 < p
  · have hnd : ¬ (p : ℤ) ∣ v + 1 := by
      rintro ⟨k, hk⟩
      have : (p : ℤ) * (k - q) = r + 1 := by linarith
      have hk0 : 0 < k - q := by
        by_contra hneg; rw [not_lt] at hneg; nlinarith
      nlinarith
    rw [ite_of_neg hnd, add_zero, show v + 1 = (r + 1) + (p : ℤ) * q by linarith,
      Int.add_mul_ediv_left _ _ hp0.ne', Int.ediv_eq_zero_of_lt (by omega) hr, zero_add]
  · have hr' : r + 1 = p := by omega
    have hd : (p : ℤ) ∣ v + 1 := ⟨q + 1, by linarith⟩
    rw [ite_of_pos hd, show v + 1 = 0 + (p : ℤ) * (q + 1) by linarith, Int.add_mul_ediv_left _ _ hp0.ne',
      Int.zero_ediv, zero_add]
end QuadraticFloor
