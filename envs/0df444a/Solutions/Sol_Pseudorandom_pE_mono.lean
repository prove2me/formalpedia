-- Prove2me | solution 1 for Pseudorandom.pE_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:12.573716+00:00
-- url     : https://prove2.me/submissions/f72451ef-487c-42cc-95c8-8a97009ae9f8

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pw_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    pE P f ≤ pE P g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (pw_nonneg hP ω)
end Pseudorandom
