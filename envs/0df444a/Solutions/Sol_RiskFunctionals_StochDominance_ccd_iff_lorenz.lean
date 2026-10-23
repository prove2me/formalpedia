-- Prove2me | solution 1 for RiskFunctionals.StochDominance.ccd_iff_lorenz
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:37:44.540068+00:00
-- url     : https://prove2.me/submissions/7499c1ca-4ed3-4b32-b355-13334e37edf8

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_IntegratedFunctions
import Definitions.Def_RiskFunctionals_StochDominance_Dominance
open MeasureTheory RiskFunctionals.StochDominance

noncomputable def g79t_mu : Measure ℝ :=
  (1/2 : ENNReal) • Measure.dirac (-2) + (1/2 : ENNReal) • Measure.dirac 0

instance g79t_mu_prob : IsProbabilityMeasure g79t_mu := by
  constructor
  simp [g79t_mu]
  exact ENNReal.inv_two_add_inv_two

theorem g79t_mu_F (u : ℝ) : distributionFunction g79t_mu u =
    (if -2 ≤ u then 1/2 else 0) + (if 0 ≤ u then 1/2 else 0) := by
  unfold distributionFunction g79t_mu
  rw [measureReal_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  by_cases h1 : -2 ≤ u <;> by_cases h2 : 0 ≤ u <;>
    simp [h1, h2, Set.indicator, ENNReal.toReal_add] <;> norm_num

theorem g79t_dirac_F (c u : ℝ) : distributionFunction (Measure.dirac c) u =
    if c ≤ u then 1 else 0 := by
  unfold distributionFunction
  rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
  by_cases h : c ≤ u <;> simp [h, Set.indicator]

theorem g79t_q_mu_lo (p : ℝ) (hp : p ∈ Set.Ioc (0:ℝ) (1/2)) :
    quantileFunction g79t_mu p = -2 := by
  unfold quantileFunction
  have : {u : ℝ | p ≤ distributionFunction g79t_mu u} = Set.Ici (-2) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_Ici, g79t_mu_F]
    obtain ⟨h0, h1⟩ := hp
    constructor
    · intro h
      by_contra hc
      have h2 : ¬ (0:ℝ) ≤ u := by intro h'; exact hc (by linarith)
      simp [hc, h2] at h; linarith
    · intro h
      by_cases h2 : (0:ℝ) ≤ u <;> simp [h, h2] <;> linarith
  rw [this, csInf_Ici]

theorem g79t_q_mu_hi (p : ℝ) (hp : p ∈ Set.Ioc (1/2:ℝ) 1) :
    quantileFunction g79t_mu p = 0 := by
  unfold quantileFunction
  have : {u : ℝ | p ≤ distributionFunction g79t_mu u} = Set.Ici 0 := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_Ici, g79t_mu_F]
    obtain ⟨h0, h1⟩ := hp
    constructor
    · intro h
      by_contra hc
      by_cases h2 : (-2:ℝ) ≤ u <;> simp [hc, h2] at h <;> linarith
    · intro h
      have h2 : (-2:ℝ) ≤ u := by linarith
      simp [h, h2]; linarith
  rw [this, csInf_Ici]

theorem g79t_q_dirac (c p : ℝ) (hp : p ∈ Set.Ioc (0:ℝ) 1) :
    quantileFunction (Measure.dirac c) p = c := by
  unfold quantileFunction
  have : {u : ℝ | p ≤ distributionFunction (Measure.dirac c) u} = Set.Ici c := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_Ici, g79t_dirac_F]
    obtain ⟨h0, h1⟩ := hp
    by_cases h : c ≤ u <;> simp [h] <;> linarith
  rw [this, csInf_Ici]

theorem g79t_iqf_mu_half : integratedQuantileFunction g79t_mu (1/2) = -1 := by
  unfold integratedQuantileFunction
  rw [setIntegral_congr_fun measurableSet_Ioc (fun p hp => g79t_q_mu_lo p hp)]
  simp

theorem g79t_iqf_mu_one : integratedQuantileFunction g79t_mu 1 = -1 := by
  unfold integratedQuantileFunction
  have hu : Set.Ioc (0:ℝ) 1 = Set.Ioc 0 (1/2) ∪ Set.Ioc (1/2) 1 :=
    (Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm
  have hA : IntegrableOn (quantileFunction g79t_mu) (Set.Ioc 0 (1/2)) := by
    refine (integrableOn_const (C := (-2:ℝ)) (by simp)).congr_fun
      (fun p hp => (g79t_q_mu_lo p hp).symm) measurableSet_Ioc
  have hB : IntegrableOn (quantileFunction g79t_mu) (Set.Ioc (1/2) 1) := by
    refine (integrableOn_const (C := (0:ℝ)) (by simp)).congr_fun
      (fun p hp => (g79t_q_mu_hi p hp).symm) measurableSet_Ioc
  rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hA hB,
    setIntegral_congr_fun measurableSet_Ioc (fun p hp => g79t_q_mu_lo p hp),
    setIntegral_congr_fun measurableSet_Ioc (fun p hp => g79t_q_mu_hi p hp)]
  simp

theorem g79t_iqf_dirac (c a : ℝ) (ha : a ∈ Set.Ioc (0:ℝ) 1) :
    integratedQuantileFunction (Measure.dirac c) a = a * c := by
  unfold integratedQuantileFunction
  rw [setIntegral_congr_fun measurableSet_Ioc (fun p hp => g79t_q_dirac c p
    ⟨hp.1, hp.2.trans ha.2⟩)]
  simp [ha.1.le]

theorem g79t_int_mu : Integrable (fun v : ℝ => v) g79t_mu := by
  unfold g79t_mu
  exact (Integrable.add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp)))

theorem g79t_mean_mu : ∫ v, v ∂g79t_mu = -1 := by
  unfold g79t_mu
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp))]
  simp [integral_smul_measure]

theorem g79t_ccd : CCD g79t_mu (Measure.dirac (-1)) := by
  intro U hU h1 h2
  unfold g79t_mu
  rw [integral_add_measure (h1.mono_measure (by unfold g79t_mu; exact Measure.le_add_right le_rfl))
    (h1.mono_measure (by unfold g79t_mu; exact Measure.le_add_left le_rfl))]
  simp [integral_smul_measure]
  have := hU.2 (Set.mem_univ (-2:ℝ)) (Set.mem_univ (0:ℝ)) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp at this
  norm_num at this ⊢
  linarith

theorem solution : ¬ (∀ (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : Integrable (fun v : ℝ => v) μ₁) (h₂ : Integrable (fun v : ℝ => v) μ₂)
    (hm₁ : ∫ v, v ∂μ₁ ≠ 0) (hm₂ : ∫ v, v ∂μ₂ ≠ 0),
    CCD μ₁ μ₂ ↔ (∀ p ∈ Set.Ioo (0 : ℝ) 1, lorenzCurve μ₁ p ≤ lorenzCurve μ₂ p) ∧
      ∫ v, v ∂μ₁ = ∫ v, v ∂μ₂) := by
  intro H
  have hd : Integrable (fun v : ℝ => v) (Measure.dirac (-1 : ℝ)) := integrable_dirac (by simp)
  have hmd : ∫ v, v ∂(Measure.dirac (-1 : ℝ)) = -1 := by simp
  have := (H g79t_mu (Measure.dirac (-1)) g79t_int_mu hd (by rw [g79t_mean_mu]; norm_num)
    (by rw [hmd]; norm_num)).1 g79t_ccd
  have h := this.1 (1/2) ⟨by norm_num, by norm_num⟩
  unfold lorenzCurve at h
  rw [g79t_iqf_mu_half, g79t_iqf_mu_one, g79t_iqf_dirac _ _ ⟨by norm_num, by norm_num⟩,
    g79t_iqf_dirac _ _ ⟨by norm_num, by norm_num⟩] at h
  norm_num at h
