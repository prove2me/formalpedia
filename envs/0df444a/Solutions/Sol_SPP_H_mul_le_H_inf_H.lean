-- Prove2me | solution 1 for SPP.H_mul_le_H_inf_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:11:48.941835+00:00
-- url     : https://prove2.me/submissions/37912ba2-d0c3-4938-a1f2-b0f0b8f8e0b0

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_H_le_H_of_dvd

set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution {m₁ m₂ : ℕ} (h : m₁ * m₂ ∣ n) :
    H h ≤ H (dvd_of_mul_right_dvd h) ⊓ H (dvd_of_mul_left_dvd h) :=
  le_inf (H_le_H_of_dvd (dvd_mul_right m₁ m₂) h) (H_le_H_of_dvd (dvd_mul_left m₂ m₁) h)
end SPP
