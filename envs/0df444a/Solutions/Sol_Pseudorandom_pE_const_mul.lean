-- Prove2me | solution 1 for Pseudorandom.pE_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:46.636679+00:00
-- url     : https://prove2.me/submissions/663f3304-0c7d-4d4b-a684-b9131fe8977e

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
theorem _root_.solution (c : ℝ) (f : (ι → α) → ℝ) : pE P (fun ω => c * f ω) = c * pE P f := by
  unfold pE
  rw [mul_sum]
  congr 1; funext ω; ring
end Pseudorandom
