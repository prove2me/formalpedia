-- Prove2me | solution 1 for OLPDual.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:16:28.755+00:00
-- url     : https://prove2.me/submissions/0ddeead0-e919-4c24-b898-ee5f010f831f

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory

theorem solution (m : ℝ) (hm : 2 ≤ m) :
    IntegrableOn (fun x : ℝ => min (Real.exp (Real.log m - x * Real.log m)) 1) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), min (Real.exp (Real.log m - x * Real.log m)) 1 ≤
      1 + 1 / Real.log 2 := by
  set a := Real.log m
  have hm_pos : 0 < m := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha_ge : Real.log 2 ≤ a := Real.log_le_log (by norm_num) hm
  have ha_pos : 0 < a := lt_of_lt_of_le hlog2 ha_ge
  let f : ℝ → ℝ := fun x => min (Real.exp (a - x * a)) 1
  have hu : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have h_eq1 : Set.EqOn f (fun _ => (1 : ℝ)) (Set.Ioc 0 1) := by
    intro x hx
    dsimp [f]
    have hxa : 0 ≤ a - x * a := by nlinarith [hx.1, hx.2]
    exact min_eq_right (Real.one_le_exp hxa)
  have h_eq2 : Set.EqOn f (fun x => Real.exp a * Real.exp (-a * x)) (Set.Ioi 1) := by
    intro x hx
    dsimp [f]
    have hx1 : 1 < x := hx
    have hxa : a - x * a ≤ 0 := by nlinarith
    rw [min_eq_left (Real.exp_le_one_iff.mpr hxa), ← Real.exp_add]
    ring_nf
  have hint1 : IntegrableOn f (Set.Ioc 0 1) := by
    rw [integrableOn_congr_fun h_eq1 measurableSet_Ioc]
    exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hint2_base : IntegrableOn (fun x => Real.exp (-a * x)) (Set.Ioi 1) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha_pos) 1
  have hint2 : IntegrableOn f (Set.Ioi 1) := by
    rw [integrableOn_congr_fun h_eq2 measurableSet_Ioi]
    exact hint2_base.const_mul (Real.exp a)
  have hint : IntegrableOn f (Set.Ioi 0) := by
    rw [hu]
    exact hint1.union hint2
  refine ⟨hint, ?_⟩
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := Set.Ioc_disjoint_Ioi le_rfl
  rw [hu, setIntegral_union hdisj measurableSet_Ioi hint1 hint2]
  have hval1 : ∫ x in Set.Ioc (0 : ℝ) 1, f x = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioc h_eq1, MeasureTheory.setIntegral_const,
      MeasureTheory.Measure.real, Real.volume_Ioc]
    norm_num
  have hval2 : ∫ x in Set.Ioi (1 : ℝ), f x = 1 / a := by
    rw [setIntegral_congr_fun measurableSet_Ioi h_eq2, integral_const_mul,
      integral_exp_mul_Ioi (neg_lt_zero.mpr ha_pos) 1]
    have h_exp : Real.exp a * (-Real.exp (-a * 1) / -a) = 1 / a := by
      have : Real.exp a * Real.exp (-a * 1) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      calc Real.exp a * (-Real.exp (-a * 1) / -a)
          = (Real.exp a * Real.exp (-a * 1)) / a := by ring
        _ = 1 / a := by rw [this]
    exact h_exp
  have hinv_le : 1 / a ≤ 1 / Real.log 2 :=
    one_div_le_one_div_of_le hlog2 ha_ge
  linarith
