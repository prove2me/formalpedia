-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_weighted_full_assignment_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:49:43.227283+00:00
-- url     : https://prove2.me/submissions/64ae6e65-f9cc-4219-9949-d9e35155d377

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (τ : V → Fin q) (hbound : ∀ e ∈ G.edgeFinset, ∀ i j, ‖W e i j - 1‖ < 1) :
    pottsWeightedPartial q G W hW Finset.univ τ ≠ 0 := by
  classical
  have hweight (e : Sym2 V) (he : e ∈ G.edgeFinset) : pottsEdgeWeight W hW τ e ≠ 0 := by
    refine Sym2.inductionOn e ?_ he
    intro u v he'
    have hh := hbound s(u,v) he' (τ u) (τ v)
    have hn : W s(u,v) (τ u) (τ v) ≠ 0 := by
      intro h
      rw [h] at hh
      norm_num at hh
    exact hn
  unfold pottsWeightedPartial
  have heq (σ : V → Fin q) : (∀ v ∈ (Finset.univ : Finset V), σ v=τ v) ↔ σ=τ := by
    simp only [Finset.mem_univ,forall_true_left,funext_iff]
  simp only [heq]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.prod_ne_zero_iff.mpr (fun e he => hweight e he)
