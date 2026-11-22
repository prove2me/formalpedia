-- Prove2me | solution 1 for Pseudorandom.pE_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:41.888872+00:00
-- url     : https://prove2.me/submissions/f1752c5e-cc12-4fc1-ad07-e7fbb4c5b647

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
theorem _root_.solution (g : ι → α → ℝ) :
    pE P (fun ω => ∏ i, g i (ω i)) = ∏ i, ∑ a, P i a * g i a := by
  unfold pE pw
  rw [Fintype.prod_sum (fun i a => P i a * g i a)]
  congr 1; funext ω
  rw [prod_mul_distrib]
end Pseudorandom
