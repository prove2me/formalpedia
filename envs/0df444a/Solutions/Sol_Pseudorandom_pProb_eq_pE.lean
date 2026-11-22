-- Prove2me | solution 1 for Pseudorandom.pProb_eq_pE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:50.029108+00:00
-- url     : https://prove2.me/submissions/2bcc15c2-7d7e-4c65-a8bf-90bc1b4d9ecc

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
theorem _root_.solution (S : (ι → α) → Prop) (g : (ι → α) → ℝ) (h1 : ∀ ω, S ω → g ω = 1)
    (h0 : ∀ ω, ¬ S ω → g ω = 0) : pProb P S = pE P g := by
  classical
  unfold pProb
  congr 1; funext ω
  by_cases hs : S ω
  · rw [if_pos hs, h1 ω hs]
  · rw [if_neg hs, h0 ω hs]
end Pseudorandom
