-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_weighted_specialization
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:49:43.145534+00:00
-- url     : https://prove2.me/submissions/2e719bfa-bb0a-49c3-880f-5b5747999820

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsWeighted
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (S : Finset V) (τ : V → Fin q) :
    let W := fun (_ : Sym2 V) (i j : Fin q) => if i=j then β else 1
    let hW : ∀ e i j, W e i j = W e j i := by intro e i j; simp [W,eq_comm]
    pottsWeightedPartial q G W hW S τ = pottsPartialZ q G β S τ := by
  classical
  dsimp only
  let W := fun (_ : Sym2 V) (i j : Fin q) => if i=j then β else 1
  have hW : ∀ e i j, W e i j = W e j i := by intro e i j; simp [W,eq_comm]
  have hedge (σ : V → Fin q) (e : Sym2 V) : pottsEdgeWeight W hW σ e =
      if Sym2.lift ⟨fun u v => σ u = σ v, fun _ _ => propext eq_comm⟩ e then β else 1 := by
    refine Sym2.inductionOn e ?_
    intro u v
    by_cases h : σ u = σ v <;> simp [pottsEdgeWeight,W,h]
  have hprod (σ : V → Fin q) : (∏ e ∈ G.edgeFinset, pottsEdgeWeight W hW σ e) = β ^ monoEdges G σ := by
    simp_rw [hedge]
    rw [← Finset.prod_filter]
    simp [monoEdges]
  unfold pottsWeightedPartial pottsPartialZ
  apply Finset.sum_congr rfl
  intro σ hσ
  split_ifs
  · exact hprod σ
  · rfl
