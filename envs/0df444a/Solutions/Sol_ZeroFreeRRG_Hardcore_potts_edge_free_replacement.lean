-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_edge_free_replacement
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:21:34.908202+00:00
-- url     : https://prove2.me/submissions/b5d173b8-a18d-4e3c-9680-3f55f133f942

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_vertex_recursion
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (W W' : Sym2 V → Fin q → Fin q → ℂ)
    (hW : ∀ e i j, W e i j = W e j i) (hW' : ∀ e i j, W' e i j = W' e j i)
    (S : Finset V) (τ : V → Fin q) (v u : V) (hv : v ∈ S) (hu : u ∉ S)
    (he : s(v,u) ∈ G.edgeFinset)
    (hother : ∀ e ≠ s(v,u), ∀ i j, W' e i j = W e i j)
    (hnz : ∀ c : Fin q, W s(v,u) (τ v) c ≠ 0) :
    pottsWeightedPartial q G W' hW' S τ =
      ∑ c : Fin q, (W' s(v,u) (τ v) c / W s(v,u) (τ v) c) *
        pottsWeightedPartial q G W hW (insert u S) (Function.update τ u c) := by
  classical
  have hvu : v ≠ u := by intro h; subst v; exact hu hv
  have hp (σ : V → Fin q) (c : Fin q) (hσv : σ v=τ v) (hσu : σ u=c) :
      (∏ e ∈ G.edgeFinset, pottsEdgeWeight W' hW' σ e) =
      (W' s(v,u) (τ v) c / W s(v,u) (τ v) c) *
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
      (W' s(v,u) (τ v) c / W s(v,u) (τ v) c) *
        ((∏ e ∈ G.edgeFinset.erase s(v,u), pottsEdgeWeight W hW σ e) * W s(v,u) (σ v) (σ u))
    rw [hσv,hσu]
    field_simp [hnz c]
  rw [potts_weighted_vertex_recursion q G W' hW' S τ u hu]
  apply Finset.sum_congr rfl
  intro c hc
  unfold pottsWeightedPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  by_cases hh : ∀ w ∈ insert u S, σ w = Function.update τ u c w
  · rw [if_pos hh,if_pos hh]
    have hσv : σ v = τ v := by
      have hh' := hh v (Finset.mem_insert_of_mem hv)
      simpa [Function.update_of_ne hvu] using hh'
    have hσu : σ u = c := by simpa using hh u (Finset.mem_insert_self _ _)
    exact hp σ c hσv hσu
  · rw [if_neg hh,if_neg hh]
    simp
