-- Prove2me | solution 1 for Pseudorandom.pE_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:32.756798+00:00
-- url     : https://prove2.me/submissions/09388ce1-1f15-4739-b31e-79a1ca2b3ecb

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
theorem _root_.solution (f g : (ι → α) → ℝ) : pE P (fun ω => f ω - g ω) = pE P f - pE P g := by
  unfold pE
  rw [← sum_sub_distrib]
  congr 1; funext ω; ring
end Pseudorandom
