-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_weighted_vertex_recursion
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:49:43.151105+00:00
-- url     : https://prove2.me/submissions/a907a594-b168-4c25-9d3b-42b727985c3b

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i) (S : Finset V) (τ : V → Fin q) (v : V) (hv : v ∉ S) :
    pottsWeightedPartial q G W hW S τ = ∑ c : Fin q, pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) := by
  classical
  unfold pottsWeightedPartial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  by_cases h : ∀ w ∈ S, σ w = τ w
  · have heq (c : Fin q) : (∀ w ∈ insert v S, σ w = Function.update τ v c w) ↔ σ v = c := by
      constructor
      · intro hh
        simpa using hh v (Finset.mem_insert_self _ _)
      · intro hc w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simpa using hc
        · have hwv : w ≠ v := by intro h; subst w; exact hv hw
          simpa [Function.update_of_ne hwv] using h w hw
    rw [if_pos h]
    simp_rw [heq]
    simp
  · have heq (c : Fin q) : ¬(∀ w ∈ insert v S, σ w = Function.update τ v c w) := by
      intro hh
      apply h
      intro w hw
      have hwv : w ≠ v := by intro h; subst w; exact hv hw
      simpa [Function.update_of_ne hwv] using hh w (Finset.mem_insert_of_mem hw)
    rw [if_neg h]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro c hc
    rw [if_neg (heq c)]
