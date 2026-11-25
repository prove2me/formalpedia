-- Prove2me | solution 1 for SmallRatio.y_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:13.223248+00:00
-- url     : https://prove2.me/submissions/2318b1ed-de8b-4a82-a97a-3f5713bba22a

module
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_Legendre
public import Theorems.Thm_SmallRatio_den_congr


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
omit hh hhk hc
namespace SmallRatio
theorem _root_.solution (j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * ((-1) ^ (j + 1) * den k h j) - rem k h j := by
  have := dvd_mul_of_dvd_right (den_congr (k := k) (h := h) j) ((-1 : ℤ) ^ (j + 1))
  have e : (-1 : ℤ) ^ (j + 1) * ((h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j) =
      (h : ℤ) * ((-1) ^ (j + 1) * den k h j) - rem k h j := by
    have : ((-1 : ℤ) ^ (j + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    linear_combination (-(rem k h j : ℤ)) * this
  rwa [e] at this
end SmallRatio
