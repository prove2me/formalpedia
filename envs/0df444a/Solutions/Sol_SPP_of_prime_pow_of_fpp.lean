-- Prove2me | solution 1 for SPP.of_prime_pow_of_fpp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:10:12.964022+00:00
-- url     : https://prove2.me/submissions/39acfc16-c497-43f6-b945-63daa7d88cf9

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_of_fpp_of_mul_self_eq_one

set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution {p m : ℕ} {a : ZMod (p ^ m)} [pp : Fact p.Prime]
    (hm : 0 < m) (hp : 2 < p) (ha : FPP (p ^ m) a) :
    SPP (p ^ m) a := by
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' pp.out.one_lt
  have : Fact (1 < p ^ m) := ⟨h1⟩
  apply of_fpp_of_mul_self_eq_one ha
  intro x h
  replace h : (x + 1) * (x - 1) = 0 := by linear_combination h
  -- ℤ-ify everything
  rw [← ZMod.natCast_zmod_val x,
    show (x.val : ZMod (p ^ m)) = ((x.val : ℤ) : ZMod (p ^ m)) by norm_cast] at *
  generalize (x.val : ℤ) = y at *
  suffices (p ^ m : ℤ) ∣ y + 1 ∨ (p ^ m : ℤ) ∣ y - 1 by
    obtain (h | h) := this
    · right
      have : (y : ZMod (p ^ m)) + 1 = 0 :=
        mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (mod_cast h)
      linear_combination this
    · left
      exact_mod_cast ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (mod_cast h)).symm
  replace h : (p ^ m : ℤ) ∣ (y + 1) * (y - 1) :=
    mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (mod_cast h)
  replace pp : Prime (p : ℤ) := prime_iff_prime_int.mp pp.out
  -- p cannot divide both y + 1 and y - 1, and the result follows
  obtain (hnd | hnd) : ¬(p : ℤ) ∣ y + 1 ∨ ¬(p : ℤ) ∣ y - 1 := by
    by_contra! h
    suffices (p : ℤ) ∣ 2 by norm_cast at this; linarith [le_of_dvd (by positivity) this]
    convert (p : ℤ).dvd_sub h.1 h.2
    ring
  · right; exact pp.pow_dvd_of_dvd_mul_left m hnd h
  · left; exact pp.pow_dvd_of_dvd_mul_right m hnd h
end SPP
