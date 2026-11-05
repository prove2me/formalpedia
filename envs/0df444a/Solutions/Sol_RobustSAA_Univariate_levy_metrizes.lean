-- Prove2me | solution 1 for RobustSAA.Univariate.levy_metrizes
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:17:25.765039+00:00
-- url     : https://prove2.me/submissions/97e376c4-b1e9-42a3-81cb-0c1ba5b4e64a

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

open Filter MeasureTheory RobustSAA.Univariate Topology Set

namespace RSAA3LM

lemma cdfOf_mem (F : ProbabilityMeasure ℝ) (x : ℝ) : 0 ≤ cdfOf F x ∧ cdfOf F x ≤ 1 :=
  ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩

lemma cdfOf_mono (F : ProbabilityMeasure ℝ) : Monotone (cdfOf F) :=
  ProbabilityTheory.monotone_cdf _

lemma cdfOf_eq_real (F : ProbabilityMeasure ℝ) (x : ℝ) :
    cdfOf F x = (F : Measure ℝ).real (Iic x) :=
  ProbabilityTheory.cdf_eq_real _ x

lemma levySet_nonempty (A B : ℝ → ℝ) (hA : ∀ x, 0 ≤ A x ∧ A x ≤ 1)
    (hB : ∀ x, 0 ≤ B x ∧ B x ≤ 1) :
    ({ε : ℝ | 0 < ε ∧ ∀ ξ : ℝ, A (ξ - ε) - ε ≤ B ξ ∧ B ξ ≤ A (ξ + ε) + ε}).Nonempty := by
  refine ⟨2, by norm_num, fun ξ => ⟨?_, ?_⟩⟩
  · linarith [(hA (ξ - 2)).2, (hB ξ).1]
  · linarith [(hA (ξ + 2)).1, (hB ξ).2]

lemma levyDist_nonneg (A B : ℝ → ℝ) : 0 ≤ levyDist A B :=
  Real.sInf_nonneg (fun _ h => le_of_lt h.1)

lemma thickening_Iic_subset (c ε : ℝ) : Metric.thickening ε (Iic c) ⊆ Iic (c + ε) := by
  intro x hx
  obtain ⟨z, hz, hd⟩ := Metric.mem_thickening_iff.mp hx
  have hz' : z ≤ c := hz
  have : x - z < ε := by
    have := le_abs_self (x - z)
    rw [Real.dist_eq] at hd
    linarith
  show x ≤ c + ε
  linarith

/-- Transfer of a Lévy–Prokhorov inequality on half-lines to the cdfs. -/
lemma cdf_le_of_measure_le (μ ν : ProbabilityMeasure ℝ) (ε c : ℝ) (hε : 0 < ε)
    (h : (μ : Measure ℝ) (Iic c) ≤
      (ν : Measure ℝ) (Metric.thickening ε (Iic c)) + ENNReal.ofReal ε) :
    cdfOf μ c ≤ cdfOf ν (c + ε) + ε := by
  have h2 : (μ : Measure ℝ) (Iic c) ≤ (ν : Measure ℝ) (Iic (c + ε)) + ENNReal.ofReal ε :=
    le_trans h (add_le_add_left (measure_mono (thickening_Iic_subset c ε)) _)
  have h3 := ENNReal.toReal_mono (by finiteness) h2
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_ofReal hε.le] at h3
  rw [cdfOf_eq_real, cdfOf_eq_real]
  exact h3

lemma levy_le_of_lp (μ ν : ProbabilityMeasure ℝ) (ε : ℝ) (hε : 0 < ε)
    (h : levyProkhorovEDist (μ : Measure ℝ) (ν : Measure ℝ) < ENNReal.ofReal ε) :
    levyDist (cdfOf μ) (cdfOf ν) ≤ ε := by
  apply csInf_le ⟨0, fun _ h => le_of_lt h.1⟩
  refine ⟨hε, fun ξ => ⟨?_, ?_⟩⟩
  · have h1 := left_measure_le_of_levyProkhorovEDist_lt h
      (measurableSet_Iic : MeasurableSet (Iic (ξ - ε)))
    rw [ENNReal.toReal_ofReal hε.le] at h1
    have := cdf_le_of_measure_le μ ν ε (ξ - ε) hε h1
    rw [sub_add_cancel] at this
    linarith
  · have h1 := right_measure_le_of_levyProkhorovEDist_lt h
      (measurableSet_Iic : MeasurableSet (Iic ξ))
    rw [ENNReal.toReal_ofReal hε.le] at h1
    exact cdf_le_of_measure_le ν μ ε ξ hε h1

lemma levy_le_lpDist (μ ν : ProbabilityMeasure ℝ) :
    levyDist (cdfOf μ) (cdfOf ν) ≤ levyProkhorovDist (μ : Measure ℝ) (ν : Measure ℝ) := by
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  have h0 : 0 ≤ levyProkhorovDist (μ : Measure ℝ) (ν : Measure ℝ) := ENNReal.toReal_nonneg
  apply levy_le_of_lp μ ν _ (by linarith)
  have hne : levyProkhorovEDist (μ : Measure ℝ) (ν : Measure ℝ) ≠ ⊤ :=
    levyProkhorovEDist_ne_top _ _
  rw [← ENNReal.ofReal_toReal hne]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by
    show levyProkhorovDist (μ : Measure ℝ) (ν : Measure ℝ) <
      levyProkhorovDist (μ : Measure ℝ) (ν : Measure ℝ) + δ
    linarith)

/-- (←) step 1: Lévy convergence gives cdf convergence at continuity points. -/
lemma cdf_tendsto_of_levy (G : ℕ → ProbabilityMeasure ℝ) (F : ProbabilityMeasure ℝ)
    (h : Tendsto (fun N => levyDist (cdfOf (G N)) (cdfOf F)) atTop (nhds 0)) (x : ℝ)
    (hx : ContinuousAt (cdfOf F) x) :
    Tendsto (fun N => cdfOf (G N) x) atTop (nhds (cdfOf F x)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousAt_iff.mp hx (η / 2) (by linarith)
  set δ := min δ1 (η / 2) with hδ
  have hδpos : 0 < δ := lt_min hδ1 (by linarith)
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp h δ hδpos
  refine ⟨N0, fun N hN => ?_⟩
  have hl := hN0 N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (levyDist_nonneg _ _)] at hl
  obtain ⟨ε, ⟨hε0, hε⟩, hεlt⟩ := exists_lt_of_csInf_lt
    (levySet_nonempty _ _ (cdfOf_mem (G N)) (cdfOf_mem F)) hl
  have hεδ1 : ε < δ1 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεη : ε < η / 2 := lt_of_lt_of_le hεlt (min_le_right _ _)
  have h1 := (hε (x + ε)).1
  rw [add_sub_cancel_right] at h1
  have h2 := (hε (x - ε)).2
  rw [sub_add_cancel] at h2
  have c1 := hδ1' (show dist (x + ε) x < δ1 by
    rw [Real.dist_eq]; rw [show x + ε - x = ε by ring, abs_of_pos hε0]; exact hεδ1)
  have c2 := hδ1' (show dist (x - ε) x < δ1 by
    rw [Real.dist_eq]; rw [show x - ε - x = -ε by ring, abs_neg, abs_of_pos hε0]; exact hεδ1)
  rw [Real.dist_eq] at c1 c2 ⊢
  rw [abs_lt] at c1 c2 ⊢
  constructor <;> linarith

lemma coe_Ioc (μ : ProbabilityMeasure ℝ) (a b : ℝ) (hab : a ≤ b) :
    ((μ (Ioc a b) : NNReal) : ℝ) = cdfOf μ b - cdfOf μ a := by
  have hset : Ioc a b = Iic b \ Iic a := by
    ext y; simp only [mem_Ioc, mem_diff, mem_Iic, not_le]; tauto
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, cdfOf_eq_real, cdfOf_eq_real,
    hset, measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic]

end RSAA3LM

open RSAA3LM

theorem solution (G : ℕ → ProbabilityMeasure ℝ) (F : ProbabilityMeasure ℝ) :
    Tendsto G atTop (nhds F) ↔
      Tendsto (fun N => levyDist (cdfOf (G N)) (cdfOf F)) atTop (nhds 0) := by
  constructor
  · intro hG
    have hc := ((LevyProkhorov.probabilityMeasureHomeomorph (Ω := ℝ)).continuous.tendsto F).comp hG
    rw [tendsto_iff_dist_tendsto_zero] at hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun N => levyDist_nonneg _ _) (fun N => ?_)
    exact levy_le_lpDist (G N) F
  · intro h
    let C : ℝ → Prop := fun y => ContinuousAt (cdfOf F) y
    let S : Set (Set ℝ) := {s | ∃ a b, a ≤ b ∧ C a ∧ C b ∧ s = Ioc a b}
    have hdense : Dense {y | C y} := by
      have hcount : Set.Countable {y | ¬ C y} := (cdfOf_mono F).countable_not_continuousAt
      have := hcount.dense_compl ℝ
      simpa [compl_ofPred] using this
    apply IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem (S := S)
    · rintro s ⟨a, b, hab, ha, hb, rfl⟩ t ⟨c, d, hcd, hc, hd, rfl⟩ hne
      rw [Ioc_inter_Ioc] at hne ⊢
      obtain ⟨z, hz1, hz2⟩ := hne
      refine ⟨a ⊔ c, b ⊓ d, le_trans hz1.le hz2, ?_, ?_, rfl⟩
      · rcases le_total a c with h' | h'
        · rw [sup_eq_right.mpr h']; exact hc
        · rw [sup_eq_left.mpr h']; exact ha
      · rcases le_total b d with h' | h'
        · rw [inf_eq_left.mpr h']; exact hb
        · rw [inf_eq_right.mpr h']; exact hd
    · rintro s ⟨a, b, -, -, -, rfl⟩
      exact measurableSet_Ioc
    · intro u hu x hx
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hu x hx
      obtain ⟨a, ha, ha1, ha2⟩ := hdense.exists_between (show x - δ < x by linarith)
      obtain ⟨b, hb, hb1, hb2⟩ := hdense.exists_between (show x < x + δ by linarith)
      refine ⟨Ioc a b, ⟨a, b, by linarith, ha, hb, rfl⟩, ?_, ?_⟩
      · exact mem_of_superset (Ioo_mem_nhds ha2 hb1) Ioo_subset_Ioc_self
      · intro y hy
        apply hball
        rw [Real.ball_eq_Ioo]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · rintro s ⟨a, b, hab, ha, hb, rfl⟩
      rw [← NNReal.tendsto_coe]
      simp only [coe_Ioc _ a b hab]
      exact (cdf_tendsto_of_levy G F h b hb).sub (cdf_tendsto_of_levy G F h a ha)
