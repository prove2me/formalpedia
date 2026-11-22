-- Prove2me | solution 1 for Pseudorandom.pProb_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:18.812812+00:00
-- url     : https://prove2.me/submissions/af8b767f-860e-462a-94bc-db68afa9e4ce

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_mono

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) {S T : (ι → α) → Prop} (h : ∀ ω, S ω → T ω) :
    pProb P S ≤ pProb P T := by
  classical
  unfold pProb
  refine pE_mono hP fun ω => ?_
  by_cases hs : S ω
  · simp [hs, h ω hs]
  · simp only [hs, if_false]; split_ifs <;> norm_num
end Pseudorandom
