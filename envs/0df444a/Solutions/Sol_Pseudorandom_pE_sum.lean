-- Prove2me | solution 1 for Pseudorandom.pE_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:33.047089+00:00
-- url     : https://prove2.me/submissions/33b1183e-a405-4b59-94ee-f91363b821e8

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
theorem _root_.solution {κ : Type*} (s : Finset κ) (f : κ → (ι → α) → ℝ) :
    pE P (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, pE P (f k) := by
  unfold pE
  simp_rw [mul_sum]
  rw [sum_comm]
end Pseudorandom
