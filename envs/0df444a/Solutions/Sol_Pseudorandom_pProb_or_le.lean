-- Prove2me | solution 1 for Pseudorandom.pProb_or_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:47.396268+00:00
-- url     : https://prove2.me/submissions/e1ddcbe2-d4d2-453d-8a0e-758a1872b4ca

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_add
public import Theorems.Thm_Pseudorandom_pE_mono

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (S T : (ι → α) → Prop) :
    pProb P (fun ω => S ω ∨ T ω) ≤ pProb P S + pProb P T := by
  classical
  unfold pProb
  rw [← pE_add]
  refine pE_mono hP fun ω => ?_
  by_cases hs : S ω <;> by_cases ht : T ω <;> simp [hs, ht]
end Pseudorandom
