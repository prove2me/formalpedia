-- Prove2me | solution 1 for SeatInventory.Gaussian.protection_level_std_dev_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:13:35.326745+00:00
-- url     : https://prove2.me/submissions/3d3ac61c-bc35-4e5f-95a2-031da33c80b5

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p068e_law_eq (r σ : ℝ) :
    gaussianLaw r σ = (gaussianReal 0 1).map (fun x => σ * x + r) := by
  have hf : (fun x : ℝ => σ * x + r) = (fun x => x + r) ∘ (fun x => σ * x) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  unfold gaussianLaw
  congr 1
  · simp
  · ext; simp <;> rfl

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p068e_tail_eq {r σ : ℝ} (hσ : 0 < σ) (S : ℝ) :
    tailProb (gaussianLaw r σ) S = tailProb stdNormal ((S - r) / σ) := by
  unfold tailProb stdNormal
  rw [p068e_law_eq, Measure.map_apply (by fun_prop) measurableSet_Ici]
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_Ici]
  rw [div_le_iff₀ hσ]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p068e_strictAnti : StrictAnti (tailProb stdNormal) := by
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
theorem p068e_half : tailProb stdNormal 0 = 1 / 2 := by
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

open MeasureTheory ProbabilityTheory in
open SeatInventory.Gaussian in
theorem solution (rbar σ σ' f₁ f₂ S S' : ℝ) (hσ : 0 < σ)
    (hσσ' : σ < σ') (hf₂ : 0 < f₂) (hf : f₂ < f₁) (hS : IsProtectionLevel rbar σ f₁ f₂ S)
    (hS' : IsProtectionLevel rbar σ' f₁ f₂ S') :
    (1 / 2 < f₂ / f₁ → S' < S) ∧ (f₂ / f₁ < 1 / 2 → S < S') ∧ (f₂ / f₁ = 1 / 2 → S' = S) := by
  have hσ' : 0 < σ' := hσ.trans hσσ'
  unfold IsProtectionLevel at hS hS'
  rw [p068e_tail_eq hσ] at hS
  rw [p068e_tail_eq hσ'] at hS'
  set Z := (S - rbar) / σ with hZ
  have hZZ : (S' - rbar) / σ' = Z := p068e_strictAnti.injective (hS'.trans hS.symm)
  have e1 : S = rbar + σ * Z := by rw [hZ]; field_simp; ring
  have e2 : S' = rbar + σ' * Z := by rw [← hZZ]; field_simp; ring
  have hg := p068e_strictAnti
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : Z < 0 := by
      rw [← hg.lt_iff_gt, p068e_half, hS]; exact h
    rw [e1, e2]; nlinarith
  · have : 0 < Z := by
      rw [← hg.lt_iff_gt, p068e_half, hS]; exact h
    rw [e1, e2]; nlinarith
  · have : Z = 0 := hg.injective (by rw [p068e_half, hS, h])
    rw [e1, e2, this]; ring
