-- Prove2me | solution 1 for Pseudorandom.pProb_not_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:26.225872+00:00
-- url     : https://prove2.me/submissions/2cb808bd-e513-479b-b505-414278fdcc63

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pProb_not
public import Theorems.Thm_Pseudorandom_pProb_cylinder

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ¬ ∀ i ∈ S, ω i = x i) = 1 - ∏ i ∈ S, P i (x i) := by
  rw [pProb_not hP, pProb_cylinder hP]
end Pseudorandom
