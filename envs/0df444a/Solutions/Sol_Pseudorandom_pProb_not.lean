-- Prove2me | solution 1 for Pseudorandom.pProb_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:25.058382+00:00
-- url     : https://prove2.me/submissions/44f9ad63-ba1a-494d-b467-55a327201446

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_const
public import Theorems.Thm_Pseudorandom_pE_sub

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (S : (ι → α) → Prop) :
    pProb P (fun ω => ¬ S ω) = 1 - pProb P S := by
  classical
  unfold pProb
  have h := pE_sub (P := P) (fun _ => (1 : ℝ)) (fun ω => if S ω then 1 else 0)
  rw [pE_const hP] at h
  rw [← h]
  congr 1; funext ω
  by_cases hs : S ω <;> simp [hs]
end Pseudorandom
