-- Prove2me | solution 1 for PSOutsourcing.PartialObs.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T07:19:47.861408+00:00
-- url     : https://prove2.me/submissions/29ef6ba2-d465-415d-b5ba-548c2494b332

import Mathlib
import Definitions.Def_PSOutsourcing_PartialObs_Model

open MeasureTheory ProbabilityTheory

namespace PSOutsourcing.PartialObs

lemma pdf_tilt (s z : ℝ) :
    gaussianPDF 0 1 z * ENNReal.ofReal (xi s z) = gaussianPDF s 1 z := by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, xi, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma measurable_xi (s : ℝ) : Measurable (xi s) := by
  unfold xi
  fun_prop

lemma lintegral_tilt (s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫⁻ z in A, ENNReal.ofReal (xi s z) ∂(gaussianReal 0 1)
      = gaussianReal 0 1 ((fun z => z + s) ⁻¹' A) := by
  have h1 : ∫⁻ z in A, ENNReal.ofReal (xi s z) ∂(gaussianReal 0 1) = gaussianReal s 1 A := by
    rw [gaussianReal_apply s one_ne_zero, gaussianReal_of_var_ne_zero 0 one_ne_zero,
      setLIntegral_withDensity_eq_setLIntegral_mul _ (g := fun z => ENNReal.ofReal (xi s z))
        (measurable_gaussianPDF 0 1)
        (by exact ENNReal.measurable_ofReal.comp (measurable_xi s)) hA]
    congr 1
    funext z
    exact pdf_tilt s z
  have h2 := gaussianReal_map_add_const (μ := 0) (v := 1) s
  rw [zero_add] at h2
  rw [h1, ← h2, Measure.map_apply (measurable_add_const s) hA]

lemma xi_nonneg (s z : ℝ) : 0 ≤ xi s z := (Real.exp_pos _).le

lemma setIntegral_xi (s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ z in A, xi s z ∂(gaussianReal 0 1)
      = (gaussianReal 0 1).real ((fun z => z + s) ⁻¹' A) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (xi_nonneg s))
      (measurable_xi s).aestronglyMeasurable, lintegral_tilt s hA, measureReal_def]

lemma integral_xi (s : ℝ) : ∫ z, xi s z ∂(gaussianReal 0 1) = 1 := by
  have h := setIntegral_xi s MeasurableSet.univ
  simpa using h

lemma integrable_xi (s : ℝ) : Integrable (xi s) (gaussianReal 0 1) := by
  have : xi s = fun z => Real.exp (s * z) * Real.exp (-(s ^ 2 / 2)) := by
    funext z
    unfold xi
    rw [← Real.exp_add]
    ring_nf
  rw [this]
  exact (integrable_exp_mul_gaussianReal s).mul_const _

lemma xi_le_iff {s : ℝ} (hs : 0 < s) {db : ℝ} (hdb : 0 < db) (z : ℝ) :
    xi s z * db ≤ db ↔ z ≤ s / 2 := by
  unfold xi
  rw [mul_le_iff_le_one_left hdb, Real.exp_le_one_iff]
  constructor <;> intro h <;> nlinarith

lemma ind_eq {s : ℝ} (hs : 0 < s) {db : ℝ} (hdb : 0 < db) (z : ℝ) :
    (Set.Iic (s / 2)).indicator (fun z => 1 - xi s z) z
      = if xi s z * db ≤ db then 1 - xi s z else 0 := by
  simp only [Set.indicator, Set.mem_Iic, ← xi_le_iff hs hdb z]

lemma integral_affine (s a e : ℝ) :
    ∫ z, (a + e * xi s z) ∂(gaussianReal 0 1) = a + e := by
  rw [integral_add (integrable_const _) ((integrable_xi s).const_mul _), integral_const,
    integral_const_mul, integral_xi]
  simp

lemma integrable_ind (s c : ℝ) :
    Integrable (fun z => c * (Set.Iic (s / 2)).indicator (fun z => 1 - xi s z) z)
      (gaussianReal 0 1) :=
  (((integrable_const (1 : ℝ)).sub (integrable_xi s)).indicator measurableSet_Iic).const_mul c

lemma integral_ind (s c : ℝ) :
    ∫ z, c * (Set.Iic (s / 2)).indicator (fun z => 1 - xi s z) z ∂(gaussianReal 0 1)
      = c * ((gaussianReal 0 1).real (Set.Iic (s / 2))
              - (gaussianReal 0 1).real (Set.Iic (-(s / 2)))) := by
  rw [integral_const_mul, integral_indicator measurableSet_Iic,
    integral_sub (integrable_const _).integrableOn (integrable_xi s).integrableOn,
    setIntegral_const, setIntegral_xi s measurableSet_Iic]
  have hpre : (fun z => z + s) ⁻¹' Set.Iic (s / 2) = Set.Iic (-(s / 2)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [hpre, smul_eq_mul, mul_one]

lemma integral_form (s : ℝ) (_hs : 0 < s) (a e c : ℝ) :
    ∫ z, ((a + e * xi s z) - c * (Set.Iic (s / 2)).indicator (fun z => 1 - xi s z) z)
        ∂(gaussianReal 0 1)
      = a + e - c * ((gaussianReal 0 1).real (Set.Iic (s / 2))
              - (gaussianReal 0 1).real (Set.Iic (-(s / 2)))) := by
  have hI1 : Integrable (fun z => a + e * xi s z) (gaussianReal 0 1) :=
    (integrable_const _).add ((integrable_xi s).const_mul _)
  rw [integral_sub hI1 (integrable_ind s c), integral_affine, integral_ind]

/-- the constants: integrand = (a + e ξ) - c · 1{z ≤ s/2}(1 - ξ) -/
lemma delta_pt (P : Params) {s : ℝ} (hs : 0 < s) (hdb : 0 < P.db) (z : ℝ) :
    Go P P.kbar (payment P (xi s z * P.db)) - G P P.kbar (xi s z * P.db)
      = ((P.vo - P.v + P.C * P.kbar - P.α * P.C * P.kbar)
          + (P.C * P.kbar * P.β * P.db - P.α * P.C * P.kbar * P.β * P.db) * xi s z)
        - (P.α * P.C * P.kbar * P.β * P.db)
            * (Set.Iic (s / 2)).indicator (fun z => 1 - xi s z) z := by
  rw [ind_eq hs hdb z]
  unfold Go G payment revO rev costS cost
  split_ifs <;> ring

lemma deltaFull_pt (P : Params) (s z : ℝ) :
    Go P P.kbar (costS P P.kbar (xi s z * P.db)) - G P P.kbar (xi s z * P.db)
      = (P.vo - P.v + P.C * P.kbar - P.α * P.C * P.kbar)
          + (P.C * P.kbar * P.β * P.db - P.α * P.C * P.kbar * P.β * P.db) * xi s z := by
  unfold Go G revO rev costS cost
  ring

lemma loss_pt (P : Params) {s : ℝ} (hs : 0 < s) (hdb : 0 < P.db) (z : ℝ) :
    (if xi s z * P.db ≤ P.db
      then costS P P.kbar P.db - costS P P.kbar (xi s z * P.db) else 0)
      = (P.α * P.C * P.kbar * P.β * P.db)
            * (Set.Iic (s / 2)).indicator (fun z => 1 - xi s z) z := by
  rw [ind_eq hs hdb z]
  unfold costS cost
  split_ifs <;> ring

lemma delta_eq (P : Params) {s : ℝ} (hs : 0 < s) (hdb : 0 < P.db) :
    delta P s = (P.vo - P.v + P.C * P.kbar - P.α * P.C * P.kbar)
          + (P.C * P.kbar * P.β * P.db - P.α * P.C * P.kbar * P.β * P.db)
        - (P.α * P.C * P.kbar * P.β * P.db)
          * ((gaussianReal 0 1).real (Set.Iic (s / 2))
              - (gaussianReal 0 1).real (Set.Iic (-(s / 2)))) := by
  unfold delta
  simp_rw [delta_pt P hs hdb]
  rw [integral_form s hs]

lemma deltaFull_eq (P : Params) (s : ℝ) :
    deltaFull P s = (P.vo - P.v + P.C * P.kbar - P.α * P.C * P.kbar)
          + (P.C * P.kbar * P.β * P.db - P.α * P.C * P.kbar * P.β * P.db) := by
  unfold deltaFull
  simp_rw [deltaFull_pt P s]
  rw [integral_affine]

lemma loss_eq (P : Params) {s : ℝ} (hs : 0 < s) (hdb : 0 < P.db) :
    ∫ z, (if xi s z * P.db ≤ P.db
            then costS P P.kbar P.db - costS P P.kbar (xi s z * P.db) else 0)
        ∂(gaussianReal 0 1)
      = (P.α * P.C * P.kbar * P.β * P.db)
          * ((gaussianReal 0 1).real (Set.Iic (s / 2))
              - (gaussianReal 0 1).real (Set.Iic (-(s / 2)))) := by
  simp_rw [loss_pt P hs hdb]
  rw [integral_ind]

lemma cdf_lt {x y : ℝ} (h : x < y) :
    (gaussianReal 0 1).real (Set.Iic x) < (gaussianReal 0 1).real (Set.Iic y) := by
  rw [← Set.Iic_union_Ioc_eq_Iic h.le,
    measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  have hpos : 0 < (gaussianReal 0 1).real (Set.Ioc x y) := by
    rw [measureReal_def]
    apply ENNReal.toReal_pos
    · intro h0
      have h1 := (gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : NNReal) ≠ 0)) h0
      rw [Real.volume_Ioc] at h1
      simp at h1
      linarith
    · exact measure_ne_top _ _
  linarith

lemma gap_lt {s t : ℝ} (hst : s < t) :
    (gaussianReal 0 1).real (Set.Iic (s / 2)) - (gaussianReal 0 1).real (Set.Iic (-(s / 2)))
      < (gaussianReal 0 1).real (Set.Iic (t / 2))
          - (gaussianReal 0 1).real (Set.Iic (-(t / 2))) := by
  have h1 := cdf_lt (show s / 2 < t / 2 by linarith)
  have h2 := cdf_lt (show -(t / 2) < -(s / 2) by linarith)
  linarith

end PSOutsourcing.PartialObs

open MeasureTheory ProbabilityTheory PSOutsourcing.PartialObs in
theorem solution :
    (∀ P : Params, P.Standing →
      (∀ s : ℝ, 0 < s →
        delta P s = deltaFull P s
          - ∫ z, (if xi s z * P.db ≤ P.db
                  then costS P P.kbar P.db - costS P P.kbar (xi s z * P.db) else 0)
              ∂(gaussianReal 0 1)
        ∧ ∀ z : ℝ, 0 ≤ (if xi s z * P.db ≤ P.db
                  then costS P P.kbar P.db - costS P P.kbar (xi s z * P.db) else 0)) ∧
      StrictAntiOn (delta P) (Set.Ioi 0)) ∧
    (∃ P : Params, P.Standing ∧ P.α < 1 ∧ P.v < P.vo ∧ ∃ s : ℝ, 0 < s ∧ delta P s < 0) := by
  refine ⟨fun P hP => ?_, ?_⟩
  · obtain ⟨hC, hβ, hα, hα1, hlam, hpen, hv, hk, hdb⟩ := hP
    refine ⟨fun s hs => ⟨?_, fun z => ?_⟩, ?_⟩
    · rw [delta_eq P hs hdb, deltaFull_eq P s, loss_eq P hs hdb]
    · split_ifs with h
      · unfold costS cost
        have h' : 0 ≤ P.db - xi s z * P.db := by linarith
        have hc : 0 ≤ P.α * P.C * P.kbar * P.β := by positivity
        nlinarith [mul_nonneg hc h']
      · exact le_refl 0
    · intro s hs t ht hst
      rw [delta_eq P hs hdb, delta_eq P ht hdb]
      have hc : 0 < P.α * P.C * P.kbar * P.β * P.db := by positivity
      have hg := gap_lt hst
      nlinarith [mul_lt_mul_of_pos_left hg hc]
  · set D := (gaussianReal 0 1).real (Set.Iic ((2 : ℝ) / 2))
        - (gaussianReal 0 1).real (Set.Iic (-((2 : ℝ) / 2))) with hD
    have hDpos : 0 < D := by
      have := gap_lt (show (0 : ℝ) < 2 by norm_num)
      simp only [zero_div, neg_zero, sub_self] at this
      linarith
    have hDle : D ≤ 1 := by
      have h1 : (gaussianReal 0 1).real (Set.Iic ((2 : ℝ) / 2)) ≤ 1 := measureReal_le_one
      have h2 : 0 ≤ (gaussianReal 0 1).real (Set.Iic (-((2 : ℝ) / 2))) := measureReal_nonneg
      linarith
    let P : Params :=
      { C := 1, β := 1, α := 1 - D / 8, lam := 1, pen := 0, v := 0, vo := D / 8,
        kbar := 1, db := 1 }
    refine ⟨P, ⟨by norm_num, by norm_num, by show (0 : ℝ) < 1 - D / 8; linarith,
      by show (1 : ℝ) - D / 8 ≤ 1; linarith, by norm_num, le_refl _,
      by show (0 : ℝ) ≤ D / 8; linarith, by norm_num, by norm_num⟩,
      by show (1 : ℝ) - D / 8 < 1; linarith, by show (0 : ℝ) < D / 8; linarith, 2,
      by norm_num, ?_⟩
    rw [delta_eq P (by norm_num) (by norm_num)]
    show D / 8 - 0 + 1 * 1 - (1 - D / 8) * 1 * 1
        + (1 * 1 * 1 * 1 - (1 - D / 8) * 1 * 1 * 1 * 1) - (1 - D / 8) * 1 * 1 * 1 * 1 * D < 0
    nlinarith [mul_le_mul_of_nonneg_left hDle hDpos.le]
