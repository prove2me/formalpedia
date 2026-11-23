-- Prove2me | solution 1 for ShortBroadcastDom.corollary_6_11_integral_vs_fractional
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:36:53.486803+00:00
-- url     : https://prove2.me/submissions/18809b97-54ee-476f-bf72-dc96de7ac993

import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_tauOn
import Theorems.Thm_ShortBroadcastDom_lemma_6_10_short_certificates

open ShortBroadcastDom

theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (a : ℝ) (ha : 1 ≤ a) (hH : SubgraphDensityLE a H) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 < c v) :
    ((∀ v, 1 ≤ c v) → ∃ D : Finset V, DominatesSet H R D ∧
        (D.card : ℝ) ≤ (2 * (⌈a⌉₊ : ℝ) + 1) * tau H R c) ∧
      ∃ D : Finset V, DominatesSet H R D ∧ ∑ v ∈ D, c v ≤ (2 * (⌈a⌉₊ : ℝ) + 1) * tau H R c := by
  rcases lemma_6_10_short_certificates H a ha hH R c hc 1 Nat.one_pos with ⟨μ, hcov, hcost⟩
  let D : Finset V := Finset.univ.filter fun v => 0 < μ v
  have hdom : DominatesSet H R D := by
    intro r hr
    have hsum_pos : 0 < ∑ v ∈ closedNbhd H r, μ v := lt_of_lt_of_le Nat.zero_lt_one (hcov r hr)
    rcases Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hsum_pos) with ⟨v, hvr, hv0⟩
    refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Nat.pos_of_ne_zero hv0⟩, ?_⟩
    simp only [closedNbhd, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hvr ⊢
    rcases hvr with rfl | hadj
    · exact Or.inl rfl
    · exact Or.inr hadj.symm
  have hD_cost : ∑ v ∈ D, c v ≤ (2 * (⌈a⌉₊ : ℝ) + 1) * tau H R c := by
    have h1 : ∑ v ∈ D, c v ≤ ∑ v : V, c v * (μ v : ℝ) := by
      change ∑ v ∈ Finset.univ.filter (fun v => 0 < μ v), c v ≤ _
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : 0 < μ v
      · simp only [hv, ↓reduceIte]
        have hμ1 : (1 : ℝ) ≤ (μ v : ℝ) := by exact_mod_cast hv
        nlinarith [hc v, hμ1]
      · simp only [hv, ↓reduceIte]
        exact mul_nonneg (le_of_lt (hc v)) (Nat.cast_nonneg _)
    have heq_mul : ((1 : ℕ) : ℝ) + 2 * (⌈a⌉₊ : ℝ) = 2 * (⌈a⌉₊ : ℝ) + 1 := by push_cast; ring
    rw [heq_mul] at hcost
    exact h1.trans hcost
  refine ⟨fun hc1 => ⟨D, hdom, ?_⟩, ⟨D, hdom, hD_cost⟩⟩
  have hcard : (D.card : ℝ) ≤ ∑ v ∈ D, c v := by
    calc (D.card : ℝ) = ∑ _v ∈ D, (1 : ℝ) := by simp
      _ ≤ ∑ v ∈ D, c v := Finset.sum_le_sum (fun v _ => hc1 v)
  exact hcard.trans hD_cost
