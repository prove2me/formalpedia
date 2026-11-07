-- Prove2me | solution 1 for StatUnlearn.tof_comm_of_map_involution
-- status  : ACCEPTED   (prove)
-- author  : @2017Advanced@
-- created : 2026-11-06T20:12:04.975211+00:00
-- url     : https://prove2.me/submissions/2afd19fa-273a-4dff-bbb2-36ec17b1495a

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_su_tof
open MeasureTheory ProbabilityTheory
open StatUnlearn

theorem solution {W : Type*} [MeasurableSpace W]
    (ρ : W → W) (hinv : Function.Involutive ρ) (hρ : Measurable ρ)
    (P Q : Measure W) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Measure.map ρ P = Q) (hQ : Measure.map ρ Q = P) (t : ℝ) :
    tof P Q t = tof Q P t := by
  have hmem : ∀ β : ℝ, β ∈ {β : ℝ | ∃ φ : W → ℝ, Measurable φ ∧
      (∀ w, φ w ∈ Set.Icc (0 : ℝ) 1) ∧ (∫ w, φ w ∂P) ≤ t ∧ β = ∫ w, (1 - φ w) ∂Q}
      ↔ β ∈ {β : ℝ | ∃ φ : W → ℝ, Measurable φ ∧ (∀ w, φ w ∈ Set.Icc (0 : ℝ) 1) ∧
        (∫ w, φ w ∂Q) ≤ t ∧ β = ∫ w, (1 - φ w) ∂P} := by
    intro β
    constructor
    · rintro ⟨φ, hφm, hφ01, hφα, rfl⟩
      refine ⟨fun y => φ (ρ y), hφm.comp hρ, fun y => hφ01 (ρ y), ?_, ?_⟩
      · simp only []
        have h1 : ∫ w, φ (ρ w) ∂Q = ∫ w, φ w ∂(Measure.map ρ Q) := by
          rw [integral_map hρ.aemeasurable hφm.aestronglyMeasurable]
        rw [h1, hQ]; exact hφα
      · simp only []
        have h1 : ∫ w, (1 - φ (ρ w)) ∂P = ∫ w, (1 - φ w) ∂(Measure.map ρ P) := by
          rw [integral_map (f := fun y => 1 - φ y) hρ.aemeasurable (measurable_const.sub hφm).aestronglyMeasurable]
        rw [h1, hP]
    · rintro ⟨φ, hφm, hφ01, hφα, rfl⟩
      refine ⟨fun y => φ (ρ y), hφm.comp hρ, fun y => hφ01 (ρ y), ?_, ?_⟩
      · simp only []
        have h1 : ∫ w, φ (ρ w) ∂P = ∫ w, φ w ∂(Measure.map ρ P) := by
          rw [integral_map hρ.aemeasurable hφm.aestronglyMeasurable]
        rw [h1, hP]; exact hφα
      · simp only []
        have h1 : ∫ w, (1 - φ (ρ w)) ∂Q = ∫ w, (1 - φ w) ∂(Measure.map ρ Q) := by
          rw [integral_map (f := fun y => 1 - φ y) hρ.aemeasurable (measurable_const.sub hφm).aestronglyMeasurable]
        rw [h1, hQ]
  have : {β : ℝ | ∃ φ : W → ℝ, Measurable φ ∧ (∀ w, φ w ∈ Set.Icc (0 : ℝ) 1) ∧
      (∫ w, φ w ∂P) ≤ t ∧ β = ∫ w, (1 - φ w) ∂Q}
      = {β : ℝ | ∃ φ : W → ℝ, Measurable φ ∧ (∀ w, φ w ∈ Set.Icc (0 : ℝ) 1) ∧
        (∫ w, φ w ∂Q) ≤ t ∧ β = ∫ w, (1 - φ w) ∂P} :=
    Set.ext fun β => hmem β
  simp only [tof]
  rw [this]
