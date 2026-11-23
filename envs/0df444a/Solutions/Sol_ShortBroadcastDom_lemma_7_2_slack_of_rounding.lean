-- Prove2me | solution 1 for ShortBroadcastDom.lemma_7_2_slack_of_rounding
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:23:35.009861+00:00
-- url     : https://prove2.me/submissions/7b9e50c0-928d-4519-b6d5-147fcf239282

import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_RoundingData
import Definitions.Def_ShortBroadcastDom_tauOn
import Theorems.Thm_ShortBroadcastDom_lemma_7_1_rounding_calculation

open ShortBroadcastDom

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : RoundingData V) (hset : IsRoundingSetting G d) (hdens : SubgraphDensityLE d.a G)
    (hH : ∀ v ∈ d.H G, d.c v = d.b) (hO : ∀ v ∈ d.O G, (d.h G v : ℝ) ≤ d.c v)
    (M M' : ℝ) (hM : 0 < M) (hM' : 0 < M')
    (hD : ((d.D G).card : ℝ) ≤ M * ((d.wCard : ℝ) + (d.ell G : ℝ)) + M' * d.P G)
    (hC : d.cost ≤ (1 + min (1 / ((d.a + 1) * M)) (1 / M')) * tauOn G d.C d.R0 d.c) :
    ((d.D G).card : ℝ) ≤ tauOn G d.C d.R0 d.c := by
  have h71 := lemma_7_1_rounding_calculation G d hset hdens hH hO
  have hineq21 : ((d.wCard : ℝ) + (d.ell G : ℝ)) / (d.a + 1) + d.P G ≤
      d.cost - ((d.D G).card : ℝ) := h71.2.2.2
  have ha : 1 ≤ d.a := hset.1
  have ha1_pos : 0 < d.a + 1 := by linarith
  set δ : ℝ := min (1 / ((d.a + 1) * M)) (1 / M')
  have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ_le1 : δ ≤ 1 / ((d.a + 1) * M) := min_le_left _ _
  have hδ_le2 : δ ≤ 1 / M' := min_le_right _ _
  have hwl_nonneg : 0 ≤ (d.wCard : ℝ) + (d.ell G : ℝ) := by positivity
  have hP_nonneg : 0 ≤ d.P G := by
    apply Finset.sum_nonneg
    intro v hvO
    have hvC : v ∈ d.C := (Finset.mem_sdiff.mp hvO).1
    have hx0 : 0 ≤ d.x v := (hset.2.2.2.1 v hvC).1
    have hch : 0 ≤ d.c v - (d.h G v : ℝ) := by linarith [hO v hvO]
    exact mul_nonneg hch hx0
  have hterm1 : δ * (M * ((d.wCard : ℝ) + (d.ell G : ℝ))) ≤
      ((d.wCard : ℝ) + (d.ell G : ℝ)) / (d.a + 1) := by
    have h1 : δ * M ≤ (1 / ((d.a + 1) * M)) * M :=
      mul_le_mul_of_nonneg_right hδ_le1 (le_of_lt hM)
    have h2 : (1 / ((d.a + 1) * M)) * M = 1 / (d.a + 1) := by
      field_simp
    calc δ * (M * ((d.wCard : ℝ) + (d.ell G : ℝ)))
        = (δ * M) * ((d.wCard : ℝ) + (d.ell G : ℝ)) := by ring
      _ ≤ (1 / (d.a + 1)) * ((d.wCard : ℝ) + (d.ell G : ℝ)) :=
          mul_le_mul_of_nonneg_right (h1.trans_eq h2) hwl_nonneg
      _ = ((d.wCard : ℝ) + (d.ell G : ℝ)) / (d.a + 1) := by ring
  have hterm2 : δ * (M' * d.P G) ≤ d.P G := by
    have h1 : δ * M' ≤ (1 / M') * M' :=
      mul_le_mul_of_nonneg_right hδ_le2 (le_of_lt hM')
    have h2 : (1 / M') * M' = 1 := by field_simp
    calc δ * (M' * d.P G)
        = (δ * M') * d.P G := by ring
      _ ≤ 1 * d.P G := mul_le_mul_of_nonneg_right (h1.trans_eq h2) hP_nonneg
      _ = d.P G := one_mul _
  have hslack : (1 + δ) * ((d.D G).card : ℝ) ≤ d.cost := by
    have hmulD : δ * ((d.D G).card : ℝ) ≤
        δ * (M * ((d.wCard : ℝ) + (d.ell G : ℝ))) + δ * (M' * d.P G) := by
      have := mul_le_mul_of_nonneg_left hD (le_of_lt hδ_pos)
      linarith
    linarith [hmulD, hterm1, hterm2, hineq21]
  have h1δ_pos : 0 < 1 + δ := by linarith
  exact le_of_mul_le_mul_left (hslack.trans hC) h1δ_pos
