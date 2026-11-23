-- Prove2me | solution 1 for SPP.fpp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:04:21.868285+00:00
-- url     : https://prove2.me/submissions/fb196e7c-0781-424c-b879-305f6c1abc37

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
theorem _root_.solution {n : ℕ} {a : ZMod n} (h : SPP n a) :
    FPP n a := by
  rw [FPP, ← two_pow_val₂_mul_oddPart (n - 1)]
  rcases h with h | ⟨s, hs, h⟩
  · rw [mul_comm, pow_mul, h, one_pow]
  · rw [← Nat.sub_add_cancel hs.le, pow_add, mul_rotate, pow_mul, h,
      ← succ_pred (sub_ne_zero_of_lt hs), Nat.pow_succ, mul_comm, pow_mul, neg_one_sq, one_pow]
end SPP
