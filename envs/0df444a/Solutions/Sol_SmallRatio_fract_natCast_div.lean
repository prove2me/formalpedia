-- Prove2me | solution 1 for SmallRatio.fract_natCast_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:15:21.010532+00:00
-- url     : https://prove2.me/submissions/bf4cfef2-3bb4-46e6-91bf-6cb5ae05b99c

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (n k : ℕ) (hk : 0 < k) :
    Int.fract ((n : ℚ) / k) = ((n % k : ℕ) : ℚ) / k := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h0 : ((n : ℕ) : ℚ) = ((n % k : ℕ) : ℚ) + (k : ℚ) * ((n / k : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mod_add_div n k).symm
  have h1 : (n : ℚ) / k = ((n % k : ℕ) : ℚ) / k + ((n / k : ℕ) : ℤ) := by
    rw [Int.cast_natCast]
    nth_rewrite 1 [h0]
    field_simp
  rw [h1, Int.fract_add_intCast]
  apply Int.fract_eq_self.2
  constructor
  · positivity
  · rw [div_lt_one (by exact_mod_cast hk)]
    exact_mod_cast Nat.mod_lt n hk
end SmallRatio
