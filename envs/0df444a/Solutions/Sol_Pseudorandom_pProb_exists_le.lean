-- Prove2me | solution 1 for Pseudorandom.pProb_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:12.866464+00:00
-- url     : https://prove2.me/submissions/6f6b9345-e962-4001-9829-13b113420e8f

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_sum
public import Theorems.Thm_Pseudorandom_pE_mono

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution {κ : Type*} (hP : IsPMF P) (s : Finset κ) (S : κ → (ι → α) → Prop) :
    pProb P (fun ω => ∃ k ∈ s, S k ω) ≤ ∑ k ∈ s, pProb P (S k) := by
  classical
  unfold pProb
  rw [← pE_sum]
  refine pE_mono hP fun ω => ?_
  split_ifs with h
  · obtain ⟨k, hk, hS⟩ := h
    calc (1 : ℝ) = if S k ω then 1 else 0 := by simp [hS]
      _ ≤ ∑ k ∈ s, if S k ω then (1 : ℝ) else 0 :=
          single_le_sum (f := fun k => if S k ω then (1 : ℝ) else 0)
            (fun k _ => by show (0:ℝ) ≤ if S k ω then 1 else 0; split_ifs <;> norm_num) hk
  · exact sum_nonneg fun k _ => by split_ifs <;> norm_num
end Pseudorandom
