-- Prove2me | solution 1 for SPP.H_lt_H_inf_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:18:03.841876+00:00
-- url     : https://prove2.me/submissions/6e7fd692-9112-43b1-8858-e580ed450a8d

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_H_one
import Theorems.Thm_SPP_H_inf_H_lt_H_inf_H_inf_H

set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution {m₁ m₂ : ℕ} [NeZero n] (h₁ : 2 < m₁) (h₂ : 2 < m₂)
    (hc : m₁.Coprime m₂) (h : m₁ * m₂ ∣ n) :
    H h < H (dvd_of_mul_right_dvd h) ⊓ H (dvd_of_mul_left_dvd h) := by
  rw [← inf_top_eq (a := H h), ← inf_top_eq (a := H _ ⊓ H _), ← H_one]
  apply H_inf_H_lt_H_inf_H_inf_H h₁ h₂ <;> rwa [mul_one]
end SPP
