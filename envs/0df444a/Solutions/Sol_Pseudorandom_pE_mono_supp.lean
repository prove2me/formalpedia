-- Prove2me | solution 1 for Pseudorandom.pE_mono_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:41.219303+00:00
-- url     : https://prove2.me/submissions/aac5fd2f-76f1-4345-9411-a2b216cfef22

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
theorem _root_.solution (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, 0 < pw P ω → f ω ≤ g ω) :
    pE P f ≤ pE P g := by
  refine sum_le_sum fun ω _ => ?_
  rcases (pw_nonneg hP ω).lt_or_eq with hpos | hzero
  · exact mul_le_mul_of_nonneg_left (h ω hpos) hpos.le
  · rw [← hzero]; simp
end Pseudorandom
