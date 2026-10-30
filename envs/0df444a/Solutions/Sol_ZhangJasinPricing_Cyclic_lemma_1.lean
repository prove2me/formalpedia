-- Prove2me | solution 1 for ZhangJasinPricing.Cyclic.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:58:25.638986+00:00
-- url     : https://prove2.me/submissions/33566b7f-62e9-4fc6-b466-062778a03611

import Mathlib
import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis

open MeasureTheory
open ZhangJasinPricing.Cyclic

noncomputable def zjZero : Model Unit where
  M := 2
  K := 1
  M_ge := le_rfl
  K_ge := le_rfl
  price := fun i => if i = 0 then 1 else 0
  price_nonneg := by intro i _; split_ifs <;> norm_num
  price_order := by
    intro i j hij hj
    have hi : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst hi hj1; norm_num
  law := Measure.dirac ()
  probability := inferInstance
  cohort := fun _ _ _ _ => 0
  mean := fun _ _ => 0
  nonneg := by intros; exact le_rfl
  measurable := by intros; exact measurable_const
  integrable := by intros; exact integrable_zero _ _ _
  mean_eq := by intros; simp
  variance_finite := by intros; simp

lemma zj_avg (w : Word) : averageRevenue zjZero w = 0 := by
  simp [averageRevenue, cycleRevenue, demand, zjZero]

lemma zj_bench (m : Mode) : benchmark zjZero m = 0 := by
  unfold benchmark
  have : averageRevenue zjZero '' PolicyClass zjZero m ⊆ {0} := by
    rintro _ ⟨w, -, rfl⟩; simp [zj_avg]
  rcases (averageRevenue zjZero '' PolicyClass zjZero m).eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty]
  · rw [(Set.subset_singleton_iff_eq.mp this).resolve_left h.ne_empty, csSup_singleton]

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (D : Model Ω),
    (∃ w, Optimal D .decreasing w) ∧
    (∀ w, Optimal D .decreasing w → decreasingCycleLength w ≤ D.K + D.M - 1)) := by
  intro h
  have hopt : Optimal zjZero .decreasing [0, 1, 1] := by
    refine ⟨?_, by rw [zj_avg, zj_bench]⟩
    show Decreasing 2 [0, 1, 1]
    refine ⟨⟨by simp, by simp⟩, by simp⟩
  have := (h zjZero).2 _ hopt
  simp [decreasingCycleLength, zjZero] at this
