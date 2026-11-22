-- Prove2me | solution 1 for Pseudorandom.pE_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:51.819518+00:00
-- url     : https://prove2.me/submissions/8ce8ea72-eb96-444a-a7d0-0baea3d81566

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_const
public import Theorems.Thm_Pseudorandom_pE_mono

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) {f : (ι → α) → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ pE P f := by
  have := pE_mono hP (f := fun _ => (0 : ℝ)) h
  rwa [pE_const hP] at this
end Pseudorandom
