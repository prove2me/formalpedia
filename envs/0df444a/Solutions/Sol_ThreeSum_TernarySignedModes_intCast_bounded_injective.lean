-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.intCast_bounded_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:45.243374+00:00
-- url     : https://prove2.me/submissions/13b642d7-0c90-4738-9c7e-68158128e9f1

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {radix p : ℕ} {x y : ℤ}
    (hp : 2*radix<p) (hx : |x| ≤ (radix : ℤ)) (hy : |y| ≤ (radix : ℤ))
    (hxy : (x : ZMod p)=(y : ZMod p)) : x=y := by
  have hz : ((x-y : ℤ) : ZMod p)=0 := by simpa using sub_eq_zero.mpr hxy
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (x-y) p).mp hz
  have hab : (x-y).natAbs < (p : ℤ).natAbs := by
    have hab' : |x-y| < (p : ℤ) := by
      have hh := abs_sub x y
      have hpp : 2*(radix : ℤ)<p := by exact_mod_cast hp
      linarith
    rw [← Int.natCast_natAbs] at hab'
    have hh : (x-y).natAbs < p := by exact_mod_cast hab'
    simpa only [Int.natAbs_natCast] using hh
  exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hab)
end ThreeSum.TernarySignedModes
