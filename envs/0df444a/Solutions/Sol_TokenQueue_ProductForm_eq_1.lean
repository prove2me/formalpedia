-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:32:25.500961+00:00
-- url     : https://prove2.me/submissions/ae5a6b6d-217f-4648-9e51-a75f3e7e400b

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm

open Finset

theorem solution_eq1 {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (S : Finset T) :
    lamTot P - lamU P S = ∑ t ∈ univ \ S, lamTok P S t := by
  obtain ⟨-, -, -, hz, h1, -, -⟩ := hS
  unfold lamTot lamU lamTok
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun c => P.tok c ⊆ S)
    (fun c => P.lam c * ∑ t ∈ univ \ S, P.assign c S t)]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun c => P.tok c ⊆ S) (fun c => P.lam c)]
  have hA : ∀ c ∈ univ.filter (fun c => P.tok c ⊆ S),
      P.lam c * ∑ t ∈ univ \ S, P.assign c S t = 0 := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    rw [Finset.sum_eq_zero, mul_zero]
    intro t _
    apply hz
    simp only [mem_sdiff, not_and, not_not]
    intro ht; exact hc ht
  have hB : ∀ c ∈ univ.filter (fun c => ¬ P.tok c ⊆ S),
      P.lam c * ∑ t ∈ univ \ S, P.assign c S t = P.lam c := by
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    have hne : (P.tok c \ S).Nonempty := by
      rw [Finset.sdiff_nonempty]; exact hc
    have := h1 c S hne
    rw [Finset.sum_subset (s₁ := P.tok c \ S) (s₂ := univ \ S)] at this
    · rw [this, mul_one]
    · intro t ht; simp only [mem_sdiff, mem_univ, true_and] at ht ⊢; exact ht.2
    · intro t _ ht; exact hz c S t ht
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB]
  simp

end TokenQueue.ProductForm

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : TokenQueue.ProductForm.Params C T) (hS : P.Standing) (S : Finset T) :
    TokenQueue.ProductForm.lamTot P - TokenQueue.ProductForm.lamU P S =
      ∑ t ∈ Finset.univ \ S, TokenQueue.ProductForm.lamTok P S t :=
  TokenQueue.ProductForm.solution_eq1 P hS S
