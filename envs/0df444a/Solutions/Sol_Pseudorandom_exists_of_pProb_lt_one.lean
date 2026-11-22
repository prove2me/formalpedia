-- Prove2me | solution 1 for Pseudorandom.exists_of_pProb_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:24.124793+00:00
-- url     : https://prove2.me/submissions/e4f5deef-d541-45d5-b356-1c2562139351

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pw_nonneg
public import Theorems.Thm_Pseudorandom_sum_pw

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) {S : (ι → α) → Prop} (h : pProb P S < 1) :
    ∃ ω, 0 < pw P ω ∧ ¬ S ω := by
  classical
  by_contra hcon
  push_neg at hcon
  have : pProb P S = 1 := by
    unfold pProb pE
    have : ∑ ω, pw P ω * (if S ω then (1 : ℝ) else 0) = ∑ ω, pw P ω := by
      refine sum_congr rfl fun ω _ => ?_
      rcases (pw_nonneg hP ω).lt_or_eq with hpos | hzero
      · simp [hcon ω hpos]
      · rw [← hzero]; simp
    rw [this, sum_pw hP]
  linarith
end Pseudorandom
