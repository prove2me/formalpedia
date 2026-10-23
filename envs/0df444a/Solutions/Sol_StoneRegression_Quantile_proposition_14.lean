-- Prove2me | solution 1 for StoneRegression.Quantile.proposition_14
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:59:22.16007+00:00
-- url     : https://prove2.me/submissions/ebc52b6a-2647-4b56-b759-aa0d5bd8924e

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles



namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

lemma q14_ici (ν : Measure ℝ) [IsProbabilityMeasure ν] (a p : ℝ) (hp : 0 ≤ p)
    (h : ∀ t < a, ν (Iic t) ≤ ENNReal.ofReal p) : ENNReal.ofReal (1 - p) ≤ ν (Ici a) := by
  have hU : (⋃ n : ℕ, Iic (a - 1 / ((n:ℝ) + 1))) = Iio a := by
    ext y; simp only [mem_iUnion, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩; have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
      linarith
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨n, by linarith⟩
  have hmono : Monotone (fun n : ℕ => Iic (a - 1 / ((n:ℝ) + 1))) := by
    intro m n hmn; apply Iic_subset_Iic.2
    have : 1 / ((n:ℝ)+1) ≤ 1 / ((m:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  have h1 : ν (Iio a) ≤ ENNReal.ofReal p := by
    rw [← hU, hmono.measure_iUnion]
    exact iSup_le fun n => h _ (by have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
                                   linarith)
  have h2 : ν (Ici a) = 1 - ν (Iio a) := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
  rw [h2, ENNReal.ofReal_sub _ hp, ENNReal.ofReal_one]
  exact tsub_le_tsub_left h1 _

lemma q14_iic (ν : Measure ℝ) [IsProbabilityMeasure ν] (a p : ℝ)
    (h : ∀ t, a < t → ENNReal.ofReal p ≤ ν (Iic t)) : ENNReal.ofReal p ≤ ν (Iic a) := by
  have hU : (⋂ n : ℕ, Iic (a + 1 / ((n:ℝ) + 1))) = Iic a := by
    ext y; simp only [mem_iInter, mem_Iic]
    constructor
    · intro hy
      by_contra hc; push_neg at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
      have := hy n; linarith
    · intro hy n; have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
      linarith
  have hanti : Antitone (fun n : ℕ => Iic (a + 1 / ((n:ℝ) + 1))) := by
    intro m n hmn; apply Iic_subset_Iic.2
    have : 1 / ((n:ℝ)+1) ≤ 1 / ((m:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hmn 1
    linarith
  rw [← hU, hanti.measure_iInter (fun _ => measurableSet_Iic.nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  exact le_iInf fun n => h _ (by have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
                                 linarith)

/-- lower quantile of a probability measure: mass of `{|y| ≥ |L|}` is at least `min p (1-p)`. -/
lemma q14_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sInf {y : ℝ | p ≤ (ν (Iic y)).toReal} = 0 ∨
    ENNReal.ofReal (min p (1 - p)) ≤
      ν {y | |sInf {y : ℝ | p ≤ (ν (Iic y)).toReal}| ≤ |y|} := by
  set S := {y : ℝ | p ≤ (ν (Iic y)).toReal} with hS
  by_cases hL : sInf S = 0
  · exact Or.inl hL
  right
  have hne : S.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h; rw [h, Real.sInf_empty] at hL; exact hL rfl
  have hbdd : BddBelow S := by
    by_contra h; exact hL (Real.sInf_of_not_bddBelow h)
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · -- L < 0
    have key : ENNReal.ofReal p ≤ ν (Iic (sInf S)) := by
      apply q14_iic
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
      have hs' : p ≤ (ν (Iic s)).toReal := hs
      calc ENNReal.ofReal p ≤ ν (Iic s) := ENNReal.ofReal_le_of_le_toReal hs'
        _ ≤ ν (Iic t) := measure_mono (Iic_subset_Iic.2 hst.le)
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Iic] at hy; simp only [mem_setOf_eq]
    rw [abs_of_neg hneg, abs_of_neg (lt_of_le_of_lt hy hneg)]; linarith
  · have key : ENNReal.ofReal (1 - p) ≤ ν (Ici (sInf S)) := by
      apply q14_ici _ _ _ hp0.le
      intro t ht
      have : t ∉ S := fun hts => absurd (csInf_le hbdd hts) (not_le.2 ht)
      simp only [hS, mem_setOf_eq, not_le] at this
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hp0.le).2 this.le
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Ici] at hy; simp only [mem_setOf_eq]
    rw [abs_of_pos hpos, abs_of_pos (lt_of_lt_of_le hpos hy)]; exact hy

lemma q14_upper (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    sSup {y : ℝ | (ν (Iic y)).toReal ≤ p} = 0 ∨
    ENNReal.ofReal (min p (1 - p)) ≤
      ν {y | |sSup {y : ℝ | (ν (Iic y)).toReal ≤ p}| ≤ |y|} := by
  set S := {y : ℝ | (ν (Iic y)).toReal ≤ p} with hS
  by_cases hL : sSup S = 0
  · exact Or.inl hL
  right
  have hne : S.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h; rw [h, Real.sSup_empty] at hL; exact hL rfl
  have hbdd : BddAbove S := by
    by_contra h; exact hL (Real.sSup_of_not_bddAbove h)
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · have key : ENNReal.ofReal p ≤ ν (Iic (sSup S)) := by
      apply q14_iic
      intro t ht
      have : t ∉ S := fun hts => absurd (le_csSup hbdd hts) (not_le.2 ht)
      simp only [hS, mem_setOf_eq, not_le] at this
      exact ENNReal.ofReal_le_of_le_toReal this.le
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Iic] at hy; simp only [mem_setOf_eq]
    rw [abs_of_neg hneg, abs_of_neg (lt_of_le_of_lt hy hneg)]; linarith
  · have key : ENNReal.ofReal (1 - p) ≤ ν (Ici (sSup S)) := by
      apply q14_ici _ _ _ hp0.le
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_lt_csSup hne ht
      have hs' : (ν (Iic s)).toReal ≤ p := hs
      calc ν (Iic t) ≤ ν (Iic s) := measure_mono (Iic_subset_Iic.2 hst.le)
        _ ≤ ENNReal.ofReal p := (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hp0.le).2 hs'
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) (key.trans (measure_mono ?_))
    intro y hy; simp only [mem_Ici] at hy; simp only [mem_setOf_eq]
    rw [abs_of_pos hpos, abs_of_pos (lt_of_lt_of_le hpos hy)]; exact hy

/-- Chebyshev step: if `c ≤ ν {|a| ≤ |y|}` and `g ≥ G` on that set, then `G * c ≤ ∫ g`. -/
lemma q14_cheb (ν : Measure ℝ) (a : ℝ) (c G : ℝ≥0∞) (g : ℝ → ℝ≥0∞)
    (hc : c ≤ ν {y | |a| ≤ |y|}) (hg : ∀ y, |a| ≤ |y| → G ≤ g y) :
    G * c ≤ ∫⁻ y, g y ∂ν := by
  have hms : MeasurableSet {y : ℝ | |a| ≤ |y|} := measurableSet_le measurable_const measurable_abs
  calc G * c ≤ G * ν {y | |a| ≤ |y|} := by gcongr
    _ = ∫⁻ y, ({y : ℝ | |a| ≤ |y|}.indicator (fun _ => G)) y ∂ν := by
        rw [lintegral_indicator_const hms]
    _ ≤ ∫⁻ y, g y ∂ν := by
        apply lintegral_mono; intro y
        by_cases hy : y ∈ {y : ℝ | |a| ≤ |y|}
        · rw [indicator_of_mem hy]; exact hg y hy
        · rw [indicator_of_notMem hy]; exact zero_le'

lemma q14_point_lower (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (r : ℝ) (hr : 1 ≤ r) :
    ‖sInf {y : ℝ | p ≤ (ν (Iic y)).toReal}‖ₑ ^ r * ENNReal.ofReal (min p (1 - p)) ≤
      ∫⁻ y, ‖y‖ₑ ^ r ∂ν := by
  rcases q14_lower ν p hp0 hp1 with h | h
  · rw [h]; simp; rw [ENNReal.zero_rpow_of_pos (by linarith)]; simp
  · apply q14_cheb ν _ _ _ _ h
    intro y hy
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hy) (by linarith)

lemma q14_point_upper (ν : Measure ℝ) [IsProbabilityMeasure ν] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (r : ℝ) (hr : 1 ≤ r) :
    ‖sSup {y : ℝ | (ν (Iic y)).toReal ≤ p}‖ₑ ^ r * ENNReal.ofReal (min p (1 - p)) ≤
      ∫⁻ y, ‖y‖ₑ ^ r ∂ν := by
  rcases q14_upper ν p hp0 hp1 with h | h
  · rw [h]; simp; rw [ENNReal.zero_rpow_of_pos (by linarith)]; simp
  · apply q14_cheb ν _ _ _ _ h
    intro y hy
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hy) (by linarith)

theorem proposition_14_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (r : ℝ) (hr : 1 ≤ r) :
    ∫⁻ x, ‖lowerQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) ∧
    ∫⁻ x, ‖upperQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) := by
  have hm : Measurable (fun q : EuclideanSpace ℝ (Fin d) × ℝ => ‖q.2‖ₑ ^ r) :=
    (measurable_snd.enorm).pow_const r
  have hcpos : ENNReal.ofReal (min p (1 - p)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]  ; exact lt_min hp0 (by linarith)
  have hctop : ENNReal.ofReal (min p (1 - p)) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [Measure.lintegral_compProd hm]
  have hdiv : (∫⁻ x, ∫⁻ y, ‖(x, y).2‖ₑ ^ r ∂κ x ∂μ) / ENNReal.ofReal (min p (1 - p)) =
      ∫⁻ x, (∫⁻ y, ‖y‖ₑ ^ r ∂κ x) / ENNReal.ofReal (min p (1 - p)) ∂μ := by
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hcpos)]
  rw [hdiv]
  constructor
  · apply lintegral_mono; intro x
    rw [ENNReal.le_div_iff_mul_le (Or.inl hcpos) (Or.inl hctop)]
    exact q14_point_lower (κ x) p hp0 hp1 r hr
  · apply lintegral_mono; intro x
    rw [ENNReal.le_div_iff_mul_le (Or.inl hcpos) (Or.inl hctop)]
    exact q14_point_upper (κ x) p hp0 hp1 r hr

end StoneRegression.Quantile

open StoneRegression.Quantile
open StoneRegression.Quantile MeasureTheory ProbabilityTheory Filter Topology ENNReal NNReal

theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (r : ℝ) (hr : 1 ≤ r) :
    ∫⁻ x, ‖lowerQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) ∧
    ∫⁻ x, ‖upperQ κ p x‖ₑ ^ r ∂μ ≤
        (∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ)) / ENNReal.ofReal (min p (1 - p)) := by
  exact proposition_14_core μ κ p hp0 hp1 r hr
