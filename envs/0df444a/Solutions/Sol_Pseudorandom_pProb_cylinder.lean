-- Prove2me | solution 1 for Pseudorandom.pProb_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:08.510532+00:00
-- url     : https://prove2.me/submissions/fc63de24-12b7-4ffe-a3f8-e1c398a97100

module
public import Mathlib
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Theorems.Thm_Pseudorandom_pE_prod
public import Theorems.Thm_Pseudorandom_pProb_eq_pE

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {P : ι → α → ℝ}
namespace Pseudorandom
theorem _root_.solution (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ∀ i ∈ S, ω i = x i) = ∏ i ∈ S, P i (x i) := by
  classical
  rw [pProb_eq_pE _ (fun ω => ∏ i, (if i ∈ S then (if ω i = x i then (1 : ℝ) else 0) else 1))]
  · rw [pE_prod (fun i a => if i ∈ S then (if a = x i then (1 : ℝ) else 0) else 1)]
    have : ∀ i, ∑ a, P i a * (if i ∈ S then (if a = x i then (1 : ℝ) else 0) else 1) =
        if i ∈ S then P i (x i) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi, hP.2 i]
    simp_rw [this]
    rw [prod_ite_mem univ S, univ_inter]
  · intro ω h
    refine prod_eq_one fun i _ => ?_
    split_ifs with h1 h2 <;> simp_all
  · intro ω h
    push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    exact prod_eq_zero (mem_univ i) (by simp [hi, hne])
end Pseudorandom
