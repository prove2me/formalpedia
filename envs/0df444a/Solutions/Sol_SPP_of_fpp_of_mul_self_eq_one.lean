-- Prove2me | solution 1 for SPP.of_fpp_of_mul_self_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:04:20.891049+00:00
-- url     : https://prove2.me/submissions/08f43e02-a1db-4397-8cba-b2e58db15de0

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_P2M_two_pow_val__mul_oddPart_d784ed0aab74


set_option autoImplicit false
open Nat
open SPP
namespace SPP
theorem _root_.solution {n : ℕ} {a : ZMod n}
    (hf : FPP n a) (h : ∀ x : ZMod n, x * x = 1 → x = 1 ∨ x = -1) :
    SPP n a := by
  rw [SPP]
  rw [FPP, ← two_pow_val₂_mul_oddPart (n - 1)] at hf
  generalize oddPart (n - 1) = d, val₂ (n - 1) = s at *
  induction s with
  | zero =>
    left; rwa [Nat.pow_zero, one_mul] at hf
  | succ s ih =>
    rw [Nat.pow_succ, mul_right_comm, pow_mul, pow_two] at hf
    rcases h _ hf with h | h
    · rcases ih h with _ | ⟨s', hs', hs''⟩
      · left; assumption
      · right; exact ⟨s', by omega, hs''⟩
    · right; exact ⟨s, by omega, h⟩
end SPP
