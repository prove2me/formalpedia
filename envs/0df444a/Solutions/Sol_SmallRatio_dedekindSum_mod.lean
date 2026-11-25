-- Prove2me | solution 1 for SmallRatio.dedekindSum_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:00.414954+00:00
-- url     : https://prove2.me/submissions/9deb7166-b605-4525-9791-a3595dcc5d6d

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (h k : ℕ) (hk : 0 < k) : dedekindSum h k = dedekindSum (h % k) k := by
  unfold dedekindSum
  apply sum_congr rfl
  intro r _
  congr 1
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : (h : ℚ) = ((h % k : ℕ) : ℚ) + k * ((h / k : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mod_add_div h k).symm
  have e2 : (h : ℚ) * r / k = ((h % k : ℕ) : ℚ) * r / k + (((h / k) * r : ℕ) : ℚ) := by
    rw [e]; push_cast; field_simp
  unfold sawtooth
  rw [e2, Int.fract_add_natCast]
end SmallRatio
