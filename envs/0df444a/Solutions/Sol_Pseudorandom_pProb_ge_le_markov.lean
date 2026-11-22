-- Prove2me | solution 1 for Pseudorandom.pProb_ge_le_markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:25.753517+00:00
-- url     : https://prove2.me/submissions/c29bacb9-7c9d-432b-b4dd-b4dad9dd60b2

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_const_mul
public import Theorems.Thm_Pseudorandom_pE_mono

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) {f : (ι → α) → ℝ} (hf : ∀ ω, 0 ≤ f ω) {t : ℝ}
    (ht : 0 < t) : pProb P (fun ω => t ≤ f ω) ≤ pE P f / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold pProb
  rw [mul_comm, ← pE_const_mul]
  refine pE_mono hP fun ω => ?_
  split_ifs with h
  · linarith
  · linarith [hf ω]
end Pseudorandom
