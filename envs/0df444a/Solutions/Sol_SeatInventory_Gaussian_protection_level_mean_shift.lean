-- Prove2me | solution 1 for SeatInventory.Gaussian.protection_level_mean_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:06:38.638822+00:00
-- url     : https://prove2.me/submissions/633d64ba-1650-49de-aa1f-ca907f32b795

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4fea_law_eq (r σ : ℝ) :
    gaussianLaw r σ = (gaussianReal 0 1).map (fun x => σ * x + r) := by
  have hf : (fun x : ℝ => σ * x + r) = (fun x => x + r) ∘ (fun x => σ * x) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  unfold gaussianLaw
  congr 1
  · simp
  · ext; simp <;> rfl

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4fea_tail_eq {r σ : ℝ} (hσ : 0 < σ) (S : ℝ) :
    tailProb (gaussianLaw r σ) S = tailProb stdNormal ((S - r) / σ) := by
  unfold tailProb stdNormal
  rw [p4fea_law_eq, Measure.map_apply (by fun_prop) measurableSet_Ici]
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_Ici]
  rw [div_le_iff₀ hσ]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory SeatInventory.Gaussian in
theorem p4fea_strictAnti : StrictAnti (tailProb stdNormal) := by
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

open MeasureTheory ProbabilityTheory in
open SeatInventory.Gaussian in
theorem solution (rbar σ f₁ f₂ c S S' : ℝ) (hσ : 0 < σ) (hf₂ : 0 < f₂)
    (hf : f₂ < f₁) (hS : IsProtectionLevel rbar σ f₁ f₂ S)
    (hS' : IsProtectionLevel (rbar + c) σ f₁ f₂ S') :
    S' = S + c := by
  unfold IsProtectionLevel at hS hS'
  rw [p4fea_tail_eq hσ] at hS hS'
  have h := p4fea_strictAnti.injective (hS'.trans hS.symm)
  rw [div_left_inj' hσ.ne'] at h
  linarith
