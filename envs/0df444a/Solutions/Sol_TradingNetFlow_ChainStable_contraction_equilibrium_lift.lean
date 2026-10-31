-- Prove2me | solution 1 for TradingNetFlow.ChainStable.contraction_equilibrium_lift
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:37:32.412149+00:00
-- url     : https://prove2.me/submissions/b25cc9c8-c9d9-4a1f-bda0-a9fdcecbe4cd

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

open Finset TradingNetFlow.ChainStable

theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (X : Finset E) (pX : E → ℝ)
    (hIR : G.IsIndividuallyRational X pX) (pHat : {e : E // e ∉ X} → ℝ)
    (hCE : (G.contraction X pX).IsCompetitiveEquilibrium ∅ pHat) :
    G.IsCompetitiveEquilibrium X (fun e => if h : e ∈ X then pX e else pHat ⟨e, h⟩) := by
  set p : E → ℝ := fun e => if h : e ∈ X then pX e else pHat ⟨e, h⟩ with hp
  set H := G.contraction X pX with hH
  have hpX : ∀ e ∈ X, p e = pX e := fun e he => by simp [hp, he]
  have hpH : ∀ x : {e : E // e ∉ X}, pHat x = p x.1 := fun x => by simp [hp, x.2]
  intro i
  refine ⟨fun e he => by simp only [mem_inter, mem_univ, true_and] at he ⊢; exact he.2, ?_⟩
  intro Y' hY'
  rw [univ_inter] at hY'
  -- the part of `Y'` outside `X`, as a set of trades of `G^X`
  set S : Finset {e : E // e ∉ X} := Y'.subtype (fun e => e ∉ X) with hS
  have hSmap : S.map (Function.Embedding.subtype _) = Y'.filter (fun e => e ∉ X) :=
    Finset.subtype_map _
  have hSsub : S ⊆ univ ∩ H.delta i := by
    intro x hx
    simp only [hS, mem_subtype] at hx
    have := hY' hx
    simp only [Economy.delta, Economy.deltaOut, Economy.deltaIn, mem_union, mem_filter,
      mem_univ, true_and, mem_inter] at this ⊢
    simpa [hH, Economy.contraction] using this
  have hce := (hCE i).2 S hSsub
  have hYX : Y' ∩ X ∈ (X ∩ G.delta i).powerset := by
    rw [mem_powerset]
    intro e he
    rw [mem_inter] at he ⊢
    exact ⟨he.2, hY' he.1⟩
  -- the `G^X`-utility of `S` dominates the `G`-utility of `Y'`
  have hsumOut : ∑ e ∈ S ∩ H.deltaOut i, pHat e
      = ∑ e ∈ (Y'.filter (fun e => e ∉ X)) ∩ G.deltaOut i, p e := by
    have : S ∩ H.deltaOut i = (Y' ∩ G.deltaOut i).subtype (fun e => e ∉ X) := by
      ext x
      simp [hS, hH, Economy.deltaOut, Economy.contraction]
    rw [this, Finset.sum_congr rfl (fun x _ => hpH x), Finset.sum_subtype_eq_sum_filter]
    congr 1
    ext e; simp only [mem_filter, mem_inter]; tauto
  have hsumIn : ∑ e ∈ S ∩ H.deltaIn i, pHat e
      = ∑ e ∈ (Y'.filter (fun e => e ∉ X)) ∩ G.deltaIn i, p e := by
    have : S ∩ H.deltaIn i = (Y' ∩ G.deltaIn i).subtype (fun e => e ∉ X) := by
      ext x
      simp [hS, hH, Economy.deltaIn, Economy.contraction]
    rw [this, Finset.sum_congr rfl (fun x _ => hpH x), Finset.sum_subtype_eq_sum_filter]
    congr 1
    ext e; simp only [mem_filter, mem_inter]; tauto
  have hwS : G.w i Y' + ∑ e ∈ (Y' ∩ X) ∩ G.deltaOut i, pX e - ∑ e ∈ (Y' ∩ X) ∩ G.deltaIn i, pX e
      ≤ H.w i S := by
    have := Finset.le_sup' (fun Y =>
      G.w i (S.map (Function.Embedding.subtype _) ∪ Y)
        + ∑ e ∈ Y ∩ G.deltaOut i, pX e - ∑ e ∈ Y ∩ G.deltaIn i, pX e) hYX
    have hU : S.map (Function.Embedding.subtype _) ∪ Y' ∩ X = Y' := by
      rw [hSmap]; ext e; by_cases h : e ∈ X <;> simp [h]
    simp only [hU] at this
    exact this
  have hsplit : ∀ (D : Finset E), ∑ e ∈ Y' ∩ D, p e
      = ∑ e ∈ (Y' ∩ X) ∩ D, pX e + ∑ e ∈ (Y'.filter (fun e => e ∉ X)) ∩ D, p e := by
    intro D
    have h1 : ∑ e ∈ (Y' ∩ X) ∩ D, pX e = ∑ e ∈ (Y' ∩ X) ∩ D, p e :=
      Finset.sum_congr rfl (fun e he => (hpX e (mem_inter.1 (mem_inter.1 he).1).2).symm)
    rw [h1, ← Finset.sum_union]
    · congr 1; ext e; by_cases h : e ∈ X <;> simp [h]
    · rw [Finset.disjoint_left]; intro e h1 h2; exact (mem_filter.1 (mem_inter.1 h2).1).2 (mem_inter.1 (mem_inter.1 h1).1).2
  have hleft : G.utility i Y' p ≤ H.utility i S pHat := by
    unfold Economy.utility
    rw [hsumOut, hsumIn, hsplit, hsplit]
    linarith
  -- the `G^X`-utility of `∅` is attained inside `X`, where individual rationality applies
  have hright : H.utility i (∅ ∩ H.delta i) pHat ≤ G.utility i (X ∩ G.delta i) p := by
    simp only [empty_inter, Economy.utility, sum_empty, add_zero, sub_zero]
    rw [hH]
    simp only [Economy.contraction]
    refine Finset.sup'_le _ _ (fun Y hY => ?_)
    rw [mem_powerset] at hY
    have := (hIR i).2 Y hY
    have hX1 : ∑ e ∈ X ∩ G.delta i ∩ G.deltaOut i, p e
        = ∑ e ∈ X ∩ G.delta i ∩ G.deltaOut i, pX e :=
      Finset.sum_congr rfl (fun e he => hpX e (mem_inter.1 (mem_inter.1 he).1).1)
    have hX2 : ∑ e ∈ X ∩ G.delta i ∩ G.deltaIn i, p e
        = ∑ e ∈ X ∩ G.delta i ∩ G.deltaIn i, pX e :=
      Finset.sum_congr rfl (fun e he => hpX e (mem_inter.1 (mem_inter.1 he).1).1)
    unfold Economy.utility at this
    simp only [map_empty, empty_union]
    rw [hX1, hX2]
    exact this
  linarith
