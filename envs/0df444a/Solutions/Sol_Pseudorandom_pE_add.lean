-- Prove2me | solution 1 for Pseudorandom.pE_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:28.646788+00:00
-- url     : https://prove2.me/submissions/1b899f9a-0cb3-42e1-ab0d-5137aa317ec1

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
theorem _root_.solution (f g : (ι → α) → ℝ) : pE P (fun ω => f ω + g ω) = pE P f + pE P g := by
  unfold pE
  rw [← sum_add_distrib]
  congr 1; funext ω; ring
end Pseudorandom
