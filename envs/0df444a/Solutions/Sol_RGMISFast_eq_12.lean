-- Prove2me | solution 1 for RGMISFast.eq_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T01:03:44.302518+00:00
-- url     : https://prove2.me/submissions/7684d05c-efff-421f-b18c-2fd3b92db4e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RGMISFast_lemma_3_1
import Theorems.Thm_RGMISFast_lemma_3_2
import Theorems.Thm_RGMISFast_lemma_A_1
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (h : ℝ) (hh : 0 ≤ h) :
    rankLaw V {r | ¬ GoodEvent G Δ u (h + 8) r} ≤
        ENNReal.ofReal ((320 + 1 + 1 / 4) * Real.exp (-(h + 8))) ∧
      (320 + 1 + 1 / 4) * Real.exp (-(h + 8)) < Real.exp (-h)  := by
  have hL : 8 ≤ h + 8 := by linarith
  have ha := lemma_3_1 G Δ hΔ hdeg u (h+8) hL
  have hb := (lemma_3_2 G u (h+8)).1
  have hc := lemma_A_1 G Δ hΔ hdeg u (h+8) hL
  constructor
  · have hs : {r | ¬ GoodEvent G Δ u (h+8) r} =
        ({r | ¬ (EntryEvent G Δ u (h+8) r ∧ GrowthEvent G Δ u (h+8) r)} ∪
         {r | ¬ TopEvent G u (h+8) r}) ∪ {r | ¬ LowRankEvent G Δ u (h+8) r} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_union, GoodEvent]
      tauto
    rw [hs]
    calc
      _ ≤ (rankLaw V {r | ¬ (EntryEvent G Δ u (h+8) r ∧ GrowthEvent G Δ u (h+8) r)} +
          rankLaw V {r | ¬ TopEvent G u (h+8) r}) +
          rankLaw V {r | ¬ LowRankEvent G Δ u (h+8) r} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ (ENNReal.ofReal (320 * Real.exp (-(h+8))) + ENNReal.ofReal (Real.exp (-(h+8)))) +
          ENNReal.ofReal (Real.exp (-(h+8)) / 4) := add_le_add (add_le_add ha hb) hc
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  · have he : (320 + 1 + 1 / 4 : ℝ) < Real.exp 8 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 6
      norm_num [Finset.sum_range_succ] at h
      linarith
    have hp := mul_lt_mul_of_pos_right he (Real.exp_pos (-(h+8)))
    have hid : Real.exp 8 * Real.exp (-(h+8)) = Real.exp (-h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [hid] at hp
