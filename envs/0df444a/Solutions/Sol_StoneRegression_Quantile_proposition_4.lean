-- Prove2me | solution 1 for StoneRegression.Quantile.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:10:57.992173+00:00
-- url     : https://prove2.me/submissions/2f1806c8-1cc8-4ac1-ba66-122f254b903d

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting



namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

lemma goodset {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f) (ε : ℝ) (hε : 0 < ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ B : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet B ∧ μ B ≤ ENNReal.ofReal η ∧
      ∃ a > 0, ∀ x x', x ∉ B → x' ∉ B → ‖x' - x‖ ≤ a → |f x' - f x| ≤ ε := by
  -- truncation level
  have hT : Tendsto (fun N : ℕ => μ {x | (N : ℝ) < |f x|}) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun N : ℕ => {x | (N : ℝ) < |f x|})
      (fun N => (measurableSet_lt measurable_const hf.abs).nullMeasurableSet)
      (by intro m n hmn x hx; simp only [mem_setOf_eq] at *
          exact lt_of_le_of_lt (by exact_mod_cast hmn) hx)
      ⟨0, measure_ne_top _ _⟩
    have he : (⋂ N : ℕ, {x | (N : ℝ) < |f x|}) = ∅ := by
      ext x; simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      obtain ⟨N, hN⟩ := exists_nat_ge |f x|; exact ⟨N, hN⟩
    rw [he, measure_empty] at h; exact h
  have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨N, hN⟩ := (hT.eventually (gt_mem_nhds hη2)).exists
  set fN : EuclideanSpace ℝ (Fin d) → ℝ := fun x => max (-(N:ℝ)) (min (f x) N) with hfN
  have hfNm : Measurable fN := measurable_const.max (hf.min measurable_const)
  have hfNb : ∀ x, ‖fN x‖ ≤ N := by
    intro x; rw [Real.norm_eq_abs, abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith) (min_le_right _ _)
  have hfNi : Integrable fN μ :=
    Integrable.of_bound hfNm.aestronglyMeasurable (N : ℝ) (ae_of_all _ hfNb)
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  set e : ℝ≥0∞ := ENNReal.ofReal (η / 2) * ENNReal.ofReal (ε / 3) with he
  have he0 : e ≠ 0 := by
    rw [he]; exact mul_ne_zero hη2.ne' (ENNReal.ofReal_pos.2 hε3).ne'
  obtain ⟨g, hgc, hgi, hgcont, -⟩ := hfNi.exists_hasCompactSupport_lintegral_sub_le he0
  have hgu := hgc.uniformContinuous_of_continuous hgcont
  obtain ⟨a, ha, hau⟩ := Metric.uniformContinuous_iff.1 hgu (ε / 3) hε3
  set B := {x | (N : ℝ) < |f x|} ∪ {x | ENNReal.ofReal (ε / 3) ≤ ‖fN x - g x‖ₑ} with hB
  have hgm : Measurable g := hgcont.measurable
  have hB2m : MeasurableSet {x | ENNReal.ofReal (ε / 3) ≤ ‖fN x - g x‖ₑ} :=
    measurableSet_le measurable_const (hfNm.sub hgm).enorm
  refine ⟨B, (measurableSet_lt measurable_const hf.abs).union hB2m, ?_, a / 2, by linarith, ?_⟩
  · calc μ B ≤ μ {x | (N : ℝ) < |f x|} + μ {x | ENNReal.ofReal (ε / 3) ≤ ‖fN x - g x‖ₑ} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by
          refine add_le_add hN.le ?_
          · calc μ {x | ENNReal.ofReal (ε / 3) ≤ ‖fN x - g x‖ₑ}
                ≤ (∫⁻ x, ‖fN x - g x‖ₑ ∂μ) / ENNReal.ofReal (ε / 3) :=
                  meas_ge_le_lintegral_div (hfNm.sub hgm).enorm.aemeasurable
                    (ENNReal.ofReal_pos.2 hε3).ne' ENNReal.ofReal_ne_top
              _ ≤ e / ENNReal.ofReal (ε / 3) := by gcongr
              _ = ENNReal.ofReal (η / 2) := by
                  rw [he, ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.2 hε3).ne'
                    ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
  · intro x x' hx hx' hd
    simp only [hB, mem_union, mem_setOf_eq, not_or, not_lt, not_le] at hx hx'
    have e1 : fN x = f x := by
      simp only [hfN]; have := abs_le.1 hx.1
      rw [min_eq_left this.2, max_eq_right this.1]
    have e2 : fN x' = f x' := by
      simp only [hfN]; have := abs_le.1 hx'.1
      rw [min_eq_left this.2, max_eq_right this.1]
    have c1 : |fN x - g x| < ε / 3 := by
      have := hx.2; rw [Real.enorm_eq_ofReal_abs] at this
      exact (ENNReal.ofReal_lt_ofReal_iff hε3).1 this
    have c2 : |fN x' - g x'| < ε / 3 := by
      have := hx'.2; rw [Real.enorm_eq_ofReal_abs] at this
      exact (ENNReal.ofReal_lt_ofReal_iff hε3).1 this
    have c3 : |g x' - g x| < ε / 3 := by
      have := hau (a := x') (b := x) (by rw [dist_eq_norm]; linarith)
      rwa [Real.dist_eq] at this
    rw [← e1, ← e2]
    calc |fN x' - fN x| = |(fN x' - g x') + (g x' - g x) - (fN x - g x)| := by ring_nf
      _ ≤ |fN x' - g x'| + |g x' - g x| + |fN x - g x| := by
          refine (abs_sub _ _).trans ?_; gcongr; exact abs_add_le _ _
      _ ≤ ε := by linarith

theorem proposition_4_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ StoneRegression.Criterion.Cond1 μ W C)
    (h3 : StoneRegression.Criterion.Cond3 μ W)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f) :
    ∀ ε : ℝ, 0 < ε → TendstoInMeasure (StoneRegression.Criterion.xLaw μ)
      (fun n ω => ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then 1 else 0)) atTop (fun _ => 0) := by
  classical
  intro ε hε
  obtain ⟨C, hC1, hC⟩ := h1
  have hCpos : (0 : ℝ) < C := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC1
    linarith
  apply tendstoInMeasure_of_ne_top
  intro t ht httop
  set δ := t.toReal with hδdef
  have hδ : 0 < δ := ENNReal.toReal_pos ht.ne' httop
  rw [ENNReal.tendsto_atTop_zero]
  intro a ha
  obtain ⟨r, -, hr0, hra⟩ := ENNReal.lt_iff_exists_real_btwn.1 ha
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
  set η' := min (r / 4) (r * δ / (8 * C)) with hη'
  have hη'pos : 0 < η' := lt_min (by linarith) (by positivity)
  obtain ⟨B, hBm, hBμ, b, hb, hBu⟩ := goodset μ f hf ε hε η' hη'pos
  have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (by linarith)
  have hr4 : (0 : ℝ≥0∞) < ENNReal.ofReal (r / 4) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨N0, hN0⟩ := ENNReal.tendsto_atTop_zero.1 (h3 b hb (ENNReal.ofReal (δ / 2)) hδ2) _ hr4
  refine ⟨max N0 1, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  -- notation
  set w : (ℕ → EuclideanSpace ℝ (Fin d)) → Fin n → ℝ := fun ω i => StoneRegression.Criterion.wAt W n ω i
    with hwdef
  have hwm : ∀ i, Measurable (fun ω => w ω i) := by
    intro i
    have hm2 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
        ((ω 0), StoneRegression.Criterion.sample ω n)) :=
      Measurable.prodMk (measurable_pi_apply 0) (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
    have h3' : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) =>
        W n (ω 0) (StoneRegression.Criterion.sample ω n)) := (hW n).comp hm2
    exact (measurable_pi_apply i).comp h3'
  set A' : (ℕ → EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ := fun ω => ∑ i : Fin n,
    ‖StoneRegression.Criterion.wAt W n ω i‖ₑ *
      ((B.indicator (fun _ => (1 : ℝ≥0)) (ω (i.val + 1)) : ℝ≥0) : ℝ≥0∞) with hA'
  have hA'm : Measurable A' := by
    apply Finset.measurable_sum; intro i _
    exact (hwm i).enorm.mul (measurable_coe_nnreal_ennreal.comp
      ((measurable_const.indicator hBm).comp (measurable_pi_apply _)))
  set T : (ℕ → EuclideanSpace ℝ (Fin d)) → ℝ := fun ω => ∑ i : Fin n,
    |StoneRegression.Criterion.wAt W n ω i| * (if b < ‖ω (i.val + 1) - ω 0‖ then 1 else 0) with hTdef
  have hincl : {ω | t ≤ edist (∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then 1 else 0)) ((fun _ => (0:ℝ)) ω)} ⊆
      ((fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' B ∪
        {ω | ENNReal.ofReal (δ / 2) ≤ A' ω}) ∪
        {ω | ENNReal.ofReal (δ / 2) ≤ edist (T ω) ((fun _ => (0:ℝ)) ω)} := by
    intro ω hω
    simp only [mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero] at hω
    have hS0 : 0 ≤ ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then (1:ℝ) else 0) := by
      apply Finset.sum_nonneg; intro i _; apply mul_nonneg (abs_nonneg _); split_ifs <;> norm_num
    rw [abs_of_nonneg hS0] at hω
    have hδS : δ ≤ ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then (1:ℝ) else 0) :=
      ENNReal.toReal_le_of_le_ofReal hS0 hω
    by_cases hB0 : ω 0 ∈ B
    · left; left; exact hB0
    set Ar : ℝ := ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
      (if ω (i.val + 1) ∈ B then 1 else 0) with hAr
    have hAr0 : 0 ≤ Ar := by
      apply Finset.sum_nonneg; intro i _; apply mul_nonneg (abs_nonneg _); split_ifs <;> norm_num
    have hT0 : 0 ≤ T ω := by
      apply Finset.sum_nonneg; intro i _; apply mul_nonneg (abs_nonneg _); split_ifs <;> norm_num
    have hsplit : ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then (1:ℝ) else 0) ≤ Ar + T ω := by
      rw [hAr, hTdef, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro i _
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      by_cases hi : ε < |f (ω (i.val + 1)) - f (ω 0)|
      · rw [if_pos hi]
        by_cases hiB : ω (i.val + 1) ∈ B
        · rw [if_pos hiB]; split_ifs <;> norm_num
        · rw [if_neg hiB]
          by_cases hd : b < ‖ω (i.val + 1) - ω 0‖
          · rw [if_pos hd]; norm_num
          · exfalso
            exact absurd (hBu (ω 0) (ω (i.val + 1)) hB0 hiB (not_lt.1 hd)) (not_le.2 hi)
      · rw [if_neg hi]; split_ifs <;> norm_num
    by_cases hAc : δ / 2 ≤ Ar
    · left; right
      simp only [mem_setOf_eq]
      have : ENNReal.ofReal Ar = A' ω := by
        rw [hAr, ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl; intro i _
          rw [ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
          congr 1
          by_cases hiB : ω (i.val + 1) ∈ B
          · rw [if_pos hiB, indicator_of_mem hiB]; simp
          · rw [if_neg hiB, indicator_of_notMem hiB]; simp
        · intro i _; apply mul_nonneg (abs_nonneg _); split_ifs <;> norm_num
      rw [← this]; exact ENNReal.ofReal_le_ofReal hAc
    · right
      simp only [mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_nonneg hT0]; linarith
  -- bounds
  have hb1 : StoneRegression.Criterion.xLaw μ ((fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' B)
      ≤ ENNReal.ofReal (r / 4) := by
    have e0 : StoneRegression.Criterion.xLaw μ ((fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' B)
        = μ B :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) 0).measure_preimage hBm.nullMeasurableSet
    rw [e0]
    exact hBμ.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hb2 : StoneRegression.Criterion.xLaw μ {ω | ENNReal.ofReal (δ / 2) ≤ A' ω} ≤
      ENNReal.ofReal (r / 4) := by
    refine (meas_ge_le_lintegral_div hA'm.aemeasurable hδ2.ne' ENNReal.ofReal_ne_top).trans ?_
    apply ENNReal.div_le_of_le_mul
    have hc1 := hC (B.indicator (fun _ => (1 : ℝ≥0)))
      (measurable_const.indicator hBm) n hn1
    have hind : ∫⁻ x, ((B.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ≥0∞) ∂μ = μ B := by
      rw [show (fun x => ((B.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ≥0∞)) = B.indicator 1 from
        funext (fun x => by by_cases hx : x ∈ B <;> simp [hx])]
      exact lintegral_indicator_one hBm
    rw [hind] at hc1
    calc ∫⁻ ω, A' ω ∂(StoneRegression.Criterion.xLaw μ) ≤ C * μ B := hc1
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (r * δ / (8 * C)) := by
          rw [ENNReal.ofReal_coe_nnreal]
          gcongr
          exact hBμ.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = ENNReal.ofReal (r / 4) * ENNReal.ofReal (δ / 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp; ring
  have hb3 := hN0 n hn0
  calc _ ≤ _ := measure_mono hincl
    _ ≤ StoneRegression.Criterion.xLaw μ ((fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' B) +
        StoneRegression.Criterion.xLaw μ {ω | ENNReal.ofReal (δ / 2) ≤ A' ω} +
        StoneRegression.Criterion.xLaw μ
          {ω | ENNReal.ofReal (δ / 2) ≤ edist (T ω) ((fun _ => (0:ℝ)) ω)} := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) := by
        gcongr
    _ ≤ a := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hra.le

end StoneRegression.Quantile

open StoneRegression.Quantile
open StoneRegression.Quantile MeasureTheory ProbabilityTheory Filter Topology ENNReal NNReal

theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W)
    (h1 : ∃ C : ℝ≥0, 1 ≤ C ∧ StoneRegression.Criterion.Cond1 μ W C) (h2 : ∃ D : ℝ, 1 ≤ D ∧ StoneRegression.Criterion.Cond2 μ W D) (h3 : StoneRegression.Criterion.Cond3 μ W)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f) :
    ∀ ε : ℝ, 0 < ε → TendstoInMeasure (StoneRegression.Criterion.xLaw μ)
      (fun n ω => ∑ i : Fin n, |StoneRegression.Criterion.wAt W n ω i| *
        (if ε < |f (ω (i.val + 1)) - f (ω 0)| then 1 else 0)) atTop (fun _ => 0) := by
  exact proposition_4_core μ W hW h1 h3 f hf
