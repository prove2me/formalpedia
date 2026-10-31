-- Prove2me | solution 1 for TradingNetFlow.ChainStable.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:40:21.861843+00:00
-- url     : https://prove2.me/submissions/88f36d8b-2216-4e3e-bb3a-8677d0b0058a

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

open Finset TradingNetFlow.ChainStable

theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (hG : G.Standing) (X X' : Finset E) (p : E → ℝ)
    (hX : G.IsCompetitiveEquilibrium X p) (hX' : G.IsEfficient X') :
    G.IsCompetitiveEquilibrium X' p := by
  -- summing utilities over agents, prices cancel and total welfare remains
  have hsumu : ∀ S : Finset E, ∑ i, G.utility i (S ∩ G.delta i) p = G.welfare S := by
    intro S
    have hout : ∑ i, ∑ e ∈ S ∩ G.delta i ∩ G.deltaOut i, p e = ∑ e ∈ S, p e := by
      rw [← Finset.sum_fiberwise S G.seller p]
      refine sum_congr rfl (fun i _ => sum_congr ?_ (fun _ _ => rfl))
      ext e
      simp only [Economy.delta, Economy.deltaOut, Economy.deltaIn, mem_inter, mem_union,
        mem_filter, mem_univ, true_and]
      tauto
    have hin : ∑ i, ∑ e ∈ S ∩ G.delta i ∩ G.deltaIn i, p e = ∑ e ∈ S, p e := by
      rw [← Finset.sum_fiberwise S G.buyer p]
      refine sum_congr rfl (fun i _ => sum_congr ?_ (fun _ _ => rfl))
      ext e
      simp only [Economy.delta, Economy.deltaOut, Economy.deltaIn, mem_inter, mem_union,
        mem_filter, mem_univ, true_and]
      tauto
    unfold Economy.utility Economy.welfare
    rw [sum_sub_distrib, sum_add_distrib, hout, hin]
    ring
  have hle : ∀ i, G.utility i (X' ∩ G.delta i) p ≤ G.utility i (X ∩ G.delta i) p := by
    intro i
    apply (hX i).2
    rw [univ_inter]
    exact inter_subset_right
  have hW := hX' X
  have hzero : ∀ i ∈ (univ : Finset N),
      G.utility i (X ∩ G.delta i) p - G.utility i (X' ∩ G.delta i) p = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))).1
    rw [sum_sub_distrib, hsumu, hsumu]
    have : 0 ≤ ∑ i, (G.utility i (X ∩ G.delta i) p - G.utility i (X' ∩ G.delta i) p) :=
      sum_nonneg (fun i _ => sub_nonneg.2 (hle i))
    rw [sum_sub_distrib, hsumu, hsumu] at this
    linarith
  intro i
  refine ⟨by rw [univ_inter]; exact inter_subset_right, fun Y hY => ?_⟩
  have h1 := (hX i).2 Y hY
  have h2 := hzero i (mem_univ i)
  linarith
