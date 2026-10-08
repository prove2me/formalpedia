-- Prove2me | solution 1 for SeatInventory.Gaussian.gaussian_emsr_protection_level
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:04:07.572342+00:00
-- url     : https://prove2.me/submissions/b3041846-1166-4d5c-a0f2-8a2fd276980a

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_law_eq (r σ : ℝ) :
    gaussianLaw r σ = (gaussianReal 0 1).map (fun x => σ * x + r) := by
  have hf : (fun x : ℝ => σ * x + r) = (fun x => x + r) ∘ (fun x => σ * x) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  unfold gaussianLaw
  congr 1
  · simp
  · ext; simp <;> rfl

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_tail_eq {r σ : ℝ} (hσ : 0 < σ) (S : ℝ) :
    tailProb (gaussianLaw r σ) S = tailProb stdNormal ((S - r) / σ) := by
  unfold tailProb stdNormal
  rw [p4440_law_eq, Measure.map_apply (by fun_prop) measurableSet_Ici]
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_Ici]
  rw [div_le_iff₀ hσ]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_strictAnti : StrictAnti (tailProb stdNormal) := by
  intro a b hab
  unfold tailProb stdNormal
  have hU : Set.Ici a = Set.Ico a b ∪ Set.Ici b := (Set.Ico_union_Ici_eq_Ici hab.le).symm
  have hD : Disjoint (Set.Ico a b) (Set.Ici b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_lt.2 hx')
  rw [hU, measure_union hD measurableSet_Ici, ENNReal.toReal_add (measure_ne_top _ _)
    (measure_ne_top _ _)]
  have hpos : 0 < (gaussianReal 0 1 (Set.Ico a b)).toReal := by
    refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
    intro h0
    have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h0
    rw [Real.volume_Ico] at this
    exact absurd this (by simpa using hab)
  linarith

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_half : tailProb stdNormal 0 = 1 / 2 := by
  unfold tailProb stdNormal
  have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  have hsym : gaussianReal 0 1 (Set.Ici 0) = gaussianReal 0 1 (Set.Iio 0) := by
    have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    rw [neg_zero] at h
    have h2 : gaussianReal 0 1 (Set.Ici 0) =
        ((gaussianReal 0 1).map (fun x => -x)) (Set.Ici 0) := by rw [h]
    rw [h2, Measure.map_apply (by fun_prop) measurableSet_Ici]
    have : (fun x : ℝ => -x) ⁻¹' Set.Ici 0 = Set.Iic 0 := by
      ext x; simp
    rw [this, measure_congr Iio_ae_eq_Iic.symm]
  have hsum : gaussianReal 0 1 (Set.Ici 0) + gaussianReal 0 1 (Set.Iio 0) = 1 := by
    rw [← Set.compl_Ici, measure_add_measure_compl measurableSet_Ici, measure_univ]
  rw [← hsym] at hsum
  have h3 : 2 * (gaussianReal 0 1 (Set.Ici 0)).toReal = 1 := by
    have := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp at this
    linarith
  linarith

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_cdf_cont : Continuous (cdf (gaussianReal 0 1)) := by
  haveI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  rw [continuous_iff_continuousAt]
  intro a
  have hm := (cdf (gaussianReal 0 1)).mono
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, ((cdf (gaussianReal 0 1)).right_continuous a).mono Set.Ioi_subset_Ici_self⟩
  rw [hm.continuousWithinAt_Iio_iff_leftLim_eq]
  have h1 := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton] at h1
  have h2 := ENNReal.ofReal_eq_zero.1 h1.symm
  have h3 := hm.leftLim_le (le_refl a)
  linarith

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_tail_cdf (Z : ℝ) : tailProb stdNormal Z = 1 - cdf (gaussianReal 0 1) Z := by
  haveI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  unfold tailProb stdNormal
  rw [cdf_eq_real, measureReal_def]
  have hsum : gaussianReal 0 1 (Set.Ici Z) + gaussianReal 0 1 (Set.Iio Z) = 1 := by
    rw [← Set.compl_Ici, measure_add_measure_compl measurableSet_Ici, measure_univ]
  rw [measure_congr (Iio_ae_eq_Iic (a := Z))] at hsum
  have := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
  simp at this
  linarith

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_exists {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : ∃ Z, tailProb stdNormal Z = p := by
  set g : ℝ → ℝ := fun Z => 1 - cdf (gaussianReal 0 1) Z with hg
  have hgc : Continuous g := continuous_const.sub p4440_cdf_cont
  have htop : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have := (tendsto_cdf_atTop (gaussianReal 0 1)).const_sub (1 : ℝ)
    simpa using this
  have hbot : Filter.Tendsto g Filter.atBot (nhds 1) := by
    have := (tendsto_cdf_atBot (gaussianReal 0 1)).const_sub (1 : ℝ)
    simpa using this
  obtain ⟨b, hb⟩ := (htop.eventually (gt_mem_nhds h0)).exists
  obtain ⟨a, ha⟩ := (hbot.eventually (lt_mem_nhds h1)).exists
  obtain ⟨Z, hZ⟩ := intermediate_value_univ b a hgc ⟨hb.le, ha.le⟩
  exact ⟨Z, by rw [p4440_tail_cdf]; exact hZ⟩

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_sens (rbar σ σ' f₁ f₂ S S' : ℝ) (hσ : 0 < σ)
    (hσσ' : σ < σ') (hS : IsProtectionLevel rbar σ f₁ f₂ S)
    (hS' : IsProtectionLevel rbar σ' f₁ f₂ S') :
    (1 / 2 < f₂ / f₁ → S' < S) ∧ (f₂ / f₁ < 1 / 2 → S < S') ∧ (f₂ / f₁ = 1 / 2 → S' = S) := by
  have hσ' : 0 < σ' := hσ.trans hσσ'
  unfold IsProtectionLevel at hS hS'
  rw [p4440_tail_eq hσ] at hS
  rw [p4440_tail_eq hσ'] at hS'
  set Z := (S - rbar) / σ with hZ
  have hZZ : (S' - rbar) / σ' = Z := p4440_strictAnti.injective (hS'.trans hS.symm)
  have e1 : S = rbar + σ * Z := by rw [hZ]; field_simp; ring
  have e2 : S' = rbar + σ' * Z := by rw [← hZZ]; field_simp; ring
  have hg := p4440_strictAnti
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : Z < 0 := by
      rw [← hg.lt_iff_gt, p4440_half, hS]; exact h
    rw [e1, e2]; nlinarith
  · have : 0 < Z := by
      rw [← hg.lt_iff_gt, p4440_half, hS]; exact h
    rw [e1, e2]; nlinarith
  · have : Z = 0 := hg.injective (by rw [p4440_half, hS, h])
    rw [e1, e2, this]; ring

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_sign (f₁ f₂ Z : ℝ) (hZ : IsStdNormalLevel f₁ f₂ Z) :
    (1 / 2 < f₂ / f₁ → Z < 0) ∧ (f₂ / f₁ < 1 / 2 → 0 < Z) ∧ (f₂ / f₁ = 1 / 2 → Z = 0) := by
  unfold IsStdNormalLevel at hZ
  have hg := p4440_strictAnti
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [← hg.lt_iff_gt, p4440_half, hZ]; exact h
  · rw [← hg.lt_iff_gt, p4440_half, hZ]; exact h
  · exact hg.injective (by rw [p4440_half, hZ, h])

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4440_SZ {rbar σ f₁ f₂ S Z : ℝ} (hσ : 0 < σ) (hS : IsProtectionLevel rbar σ f₁ f₂ S)
    (hZ : IsStdNormalLevel f₁ f₂ Z) : S = rbar + Z * σ := by
  unfold IsProtectionLevel at hS
  unfold IsStdNormalLevel at hZ
  rw [p4440_tail_eq hσ] at hS
  have h : (S - rbar) / σ = Z := p4440_strictAnti.injective (hS.trans hZ.symm)
  rw [← h]; field_simp; ring

open MeasureTheory ProbabilityTheory in
open SeatInventory.Gaussian in
theorem solution (rbar σ f₁ f₂ : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) :
    (∃! S : ℝ, IsProtectionLevel rbar σ f₁ f₂ S) ∧
    (∃! Z : ℝ, IsStdNormalLevel f₁ f₂ Z) ∧
    (∀ S Z : ℝ, IsProtectionLevel rbar σ f₁ f₂ S → IsStdNormalLevel f₁ f₂ Z →
      S = rbar + Z * σ) ∧
    (∀ Z : ℝ, IsStdNormalLevel f₁ f₂ Z →
      (1 / 2 < f₂ / f₁ → Z < 0) ∧ (f₂ / f₁ < 1 / 2 → 0 < Z) ∧ (f₂ / f₁ = 1 / 2 → Z = 0)) ∧
    (f₂ / f₁ = 1 / 2 → ∀ S : ℝ, IsProtectionLevel rbar σ f₁ f₂ S → S = rbar) ∧
    (∀ σ' S S' : ℝ, σ < σ' → IsProtectionLevel rbar σ f₁ f₂ S →
      IsProtectionLevel rbar σ' f₁ f₂ S' →
      (1 / 2 < f₂ / f₁ → S' < S) ∧ (f₂ / f₁ < 1 / 2 → S < S') ∧
        (f₂ / f₁ = 1 / 2 → S' = S)) := by
  have hf₁ : 0 < f₁ := hf₂.trans hf
  have hp0 : 0 < f₂ / f₁ := div_pos hf₂ hf₁
  have hp1 : f₂ / f₁ < 1 := (div_lt_one hf₁).2 hf
  obtain ⟨Z, hZ⟩ := p4440_exists hp0 hp1
  have hZ' : IsStdNormalLevel f₁ f₂ Z := hZ
  have hSZ : IsProtectionLevel rbar σ f₁ f₂ (rbar + Z * σ) := by
    unfold IsProtectionLevel
    rw [p4440_tail_eq hσ]
    have : (rbar + Z * σ - rbar) / σ = Z := by field_simp; ring
    rw [this]; exact hZ
  refine ⟨⟨rbar + Z * σ, hSZ, fun S hS => p4440_SZ hσ hS hZ'⟩,
    ⟨Z, hZ', fun Z₂ hZ₂ => p4440_strictAnti.injective (hZ₂.trans hZ.symm)⟩,
    fun S Z₂ hS hZ₂ => p4440_SZ hσ hS hZ₂,
    fun Z₂ hZ₂ => p4440_sign f₁ f₂ Z₂ hZ₂, fun h S hS => ?_,
    fun σ' S S' hσσ' hS hS' => p4440_sens rbar σ σ' f₁ f₂ S S' hσ hσσ' hS hS'⟩
  have hz0 : Z = 0 := ((p4440_sign f₁ f₂ Z hZ').2.2) h
  rw [p4440_SZ hσ hS hZ', hz0]; ring
