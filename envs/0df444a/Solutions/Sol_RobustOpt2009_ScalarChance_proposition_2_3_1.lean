-- Prove2me | solution 1 for RobustOpt2009.ScalarChance.proposition_2_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:01:33.446835+00:00
-- url     : https://prove2.me/submissions/340c302f-2b5b-4872-914c-3121d50b5405

import Definitions.Def_RobustOpt2009_ScalarChance_Setting

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open RobustOpt2009.ScalarChance

theorem solution {L : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (ζ : Fin L → S → ℝ) (hmeas : ∀ i, Measurable (ζ i))
    (hindep : iIndepFun ζ P)
    (hmean : ∀ i, ∫ ω, ζ i ω ∂P = 0)
    (hbounded : ∀ i, ∀ᵐ ω ∂P, ζ i ω ∈ Set.Icc (-1 : ℝ) 1) (z : Fin L → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    P.real {ω | r * Real.sqrt (∑ i, (z i)^2) < ∑ i, z i * ζ i ω} ≤
      Real.exp (-(r^2 / 2)) := by
  set s := ∑ i, (z i) ^ 2 with hs
  by_cases hs0 : s = 0
  · have hz : ∀ i, z i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).1 hs0 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have : {ω | r * Real.sqrt s < ∑ i, z i * ζ i ω} = ∅ := by
      ext ω; simp [hz, hs0]
    rw [this, measureReal_empty]
    positivity
  · have hspos : 0 < s := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hs0)
    have hsub := fun i => (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i).aemeasurable
        (hbounded i) (hmean i)).const_mul (z i)
    have hind : iIndepFun (fun i ω => z i * ζ i ω) P :=
      hindep.comp (fun i x => z i * x) (fun i => measurable_const.mul measurable_id)
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s := Finset.univ)
      (fun i _ => hsub i) (ε := r * Real.sqrt s) (by positivity)
    calc P.real {ω | r * Real.sqrt s < ∑ i, z i * ζ i ω}
        ≤ P.real {ω | r * Real.sqrt s ≤ ∑ i, z i * ζ i ω} :=
          measureReal_mono (fun ω (hω : r * Real.sqrt s < _) => hω.le) (measure_ne_top _ _)
      _ ≤ _ := h
      _ = Real.exp (-(r ^ 2 / 2)) := by
          congr 1
          push_cast
          norm_num
          rw [mul_pow, Real.sq_sqrt hspos.le]
          change -(r ^ 2 * s) / (2 * ∑ x : Fin L, z x ^ 2 * 1) = -(r ^ 2 / 2)
          simp only [mul_one, ← hs]
          field_simp
