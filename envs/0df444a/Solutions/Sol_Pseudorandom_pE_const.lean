-- Prove2me | solution 1 for Pseudorandom.pE_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:38.087465+00:00
-- url     : https://prove2.me/submissions/f235dfea-1c69-4310-9af7-364523fe73a8

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_sum_pw

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (c : ℝ) : pE P (fun _ => c) = c := by
  unfold pE
  rw [← sum_mul, sum_pw hP, one_mul]
end Pseudorandom
