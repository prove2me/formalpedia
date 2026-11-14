-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_edge_fixed_replacement
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:21:35.022414+00:00
-- url     : https://prove2.me/submissions/1c1d394c-e7e0-4572-8ed5-f343e7246cf1

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W W' : Sym2 V → Fin q → Fin q → ℂ)
    (hW : ∀ e i j, W e i j = W e j i) (hW' : ∀ e i j, W' e i j = W' e j i)
    (S : Finset V) (τ : V → Fin q) (v u : V) (hv : v ∈ S) (hu : u ∈ S)
    (he : s(v,u) ∈ G.edgeFinset)
    (hother : ∀ e ≠ s(v,u), ∀ i j, W' e i j = W e i j)
    (hnz : W s(v,u) (τ v) (τ u) ≠ 0) :
    pottsWeightedPartial q G W' hW' S τ =
      (W' s(v,u) (τ v) (τ u) / W s(v,u) (τ v) (τ u)) *
        pottsWeightedPartial q G W hW S τ := by
  classical
  have hp (σ : V → Fin q) (hσv : σ v=τ v) (hσu : σ u=τ u) :
      (∏ e ∈ G.edgeFinset, pottsEdgeWeight W' hW' σ e) =
      (W' s(v,u) (τ v) (τ u) / W s(v,u) (τ v) (τ u)) *
        (∏ e ∈ G.edgeFinset, pottsEdgeWeight W hW σ e) := by
    have hx (e : Sym2 V) (h : e ≠ s(v,u)) : pottsEdgeWeight W' hW' σ e = pottsEdgeWeight W hW σ e := by
      refine Sym2.inductionOn e ?_ h
      intro x y hxy
      change W' s(x,y) (σ x) (σ y) = W s(x,y) (σ x) (σ y)
      exact hother _ hxy _ _
    have hrest : (∏ e ∈ G.edgeFinset.erase s(v,u), pottsEdgeWeight W' hW' σ e) =
        ∏ e ∈ G.edgeFinset.erase s(v,u), pottsEdgeWeight W hW σ e := by
      apply Finset.prod_congr rfl
      intro e hem
      exact hx e (Finset.ne_of_mem_erase hem)
    rw [← Finset.prod_erase_mul G.edgeFinset (fun e => pottsEdgeWeight W' hW' σ e) he,
        ← Finset.prod_erase_mul G.edgeFinset (fun e => pottsEdgeWeight W hW σ e) he, hrest]
    change (∏ e ∈ G.edgeFinset.erase s(v,u), pottsEdgeWeight W hW σ e) * W' s(v,u) (σ v) (σ u) =
      (W' s(v,u) (τ v) (τ u) / W s(v,u) (τ v) (τ u)) *
        ((∏ e ∈ G.edgeFinset.erase s(v,u), pottsEdgeWeight W hW σ e) * W s(v,u) (σ v) (σ u))
    rw [hσv,hσu]
    field_simp [hnz]
  unfold pottsWeightedPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  by_cases hh : ∀ w ∈ S, σ w = τ w
  · rw [if_pos hh,if_pos hh]
    exact hp σ (hh v hv) (hh u hu)
  · rw [if_neg hh,if_neg hh]
    simp
