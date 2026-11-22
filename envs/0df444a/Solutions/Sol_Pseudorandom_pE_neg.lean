-- Prove2me | solution 1 for Pseudorandom.pE_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:30.417907+00:00
-- url     : https://prove2.me/submissions/80ef6970-b12e-4ebc-9e31-9b579222e0cf

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_const_mul

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (f : (ι → α) → ℝ) : pE P (fun ω => -f ω) = -pE P f := by
  have := pE_const_mul (P := P) (-1) f
  simpa using this
end Pseudorandom
