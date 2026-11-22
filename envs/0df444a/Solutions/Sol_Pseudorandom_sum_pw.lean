-- Prove2me | solution 1 for Pseudorandom.sum_pw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:29.494097+00:00
-- url     : https://prove2.me/submissions/5285b32d-1760-4454-a6d6-cacfedb9dff3

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) : ∑ ω, pw P ω = 1 := by
  unfold pw
  rw [← Fintype.prod_sum (fun i a => P i a)]
  simp [hP.2]
end Pseudorandom
