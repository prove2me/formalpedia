-- Prove2me | solution 1 for SmallRatio.sawtooth_natCast_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:21:48.445714+00:00
-- url     : https://prove2.me/submissions/59a95551-2dcb-4d85-af48-f5a08211ea7f

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
public import Theorems.Thm_SmallRatio_fract_natCast_div

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (n k : ℕ) (hk : 0 < k) (hn : ¬ k ∣ n) :
    sawtooth ((n : ℚ) / k) = ((n % k : ℕ) : ℚ) / k - 1 / 2 := by
  unfold sawtooth
  rw [fract_natCast_div n k hk, if_neg]
  have : n % k ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [div_eq_zero_iff]
  push Not
  exact ⟨by exact_mod_cast this, hk'⟩
end SmallRatio
