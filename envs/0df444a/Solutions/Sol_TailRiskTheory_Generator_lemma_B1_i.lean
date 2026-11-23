-- Prove2me | solution 1 for TailRiskTheory.Generator.lemma_B1_i
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:22:38.287927+00:00
-- url     : https://prove2.me/submissions/0a73dda1-5364-41c6-a6a8-378b834ce595

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.TailConv (Linf)
open TailRiskTheory.Generator

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (X Z : Ω → ℝ) (hX : X ∈ Linf P) (hZ : Z ∈ Linf P) (hXZ : IsPMixOf P p X Z) :
    IsPTailOf P p Z X := by
  obtain ⟨hXm, C, hC⟩ := hX
  have hdist0 : ∀ x, x < essInfRV P X → distFn P X x = 0 := by
    intro x hx
    by_contra hne
    have hpos : 0 < distFn P X x := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    have hbdd : BddBelow {y : ℝ | 0 < distFn P X y} := by
      refine ⟨-C, fun y hy => ?_⟩
      by_contra hy'
      push Not at hy'
      have hnull : P {ω | X ω ≤ y} = 0 := by
        apply measure_mono_null _ (ae_iff.mp hC)
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro habs
        have := (abs_le.mp habs).1
        linarith
      have h0 : distFn P X y = 0 := by
        simp [distFn, Measure.real, hnull]
      simp only [Set.mem_setOf_eq] at hy
      linarith
    have := csInf_le hbdd (show x ∈ {y : ℝ | 0 < distFn P X y} from hpos)
    unfold essInfRV at hx
    linarith
  intro x
  have h := hXZ x
  unfold tailDistFn
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  by_cases hm : essInfRV P X ≤ x
  · rw [if_pos hm] at h
    have hF : 0 ≤ distFn P X x := measureReal_nonneg
    rw [h, show p * 1 + (1 - p) * distFn P X x - p = (1 - p) * distFn P X x by ring,
      max_eq_left (mul_nonneg hp1'.le hF)]
    field_simp
  · rw [if_neg hm] at h
    have h0 := hdist0 x (lt_of_not_ge hm)
    rw [h, h0, max_eq_right (by linarith)]
    simp
