-- Prove2me | solution 1 for TailRiskSharing.TailConv.lemma1_tail_max
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:38:49.346675+00:00
-- url     : https://prove2.me/submissions/2af27db3-ab97-4379-abe6-66d8801dc5f9

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting

set_option autoImplicit false
open MeasureTheory TailRiskSharing.TailConv

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (X : Ω → ℝ) (hX : X ∈ Linf P)
    (m : ℝ) (hmL : TailRiskSharing.VaRConv.VaRL P ε X ≤ m) (hmR : m ≤ TailRiskSharing.VaRConv.VaRR P ε X) :
    TailRiskSharing.VaRTail.TailEquiv P ε (fun ω => max (X ω) m) X := by
  obtain ⟨hmeas, C, hC⟩ := hX
  intro x
  by_cases hxm : m ≤ x
  · have : TailRiskSharing.VaRConv.distFn P (fun ω => max (X ω) m) x = TailRiskSharing.VaRConv.distFn P X x := by
      unfold TailRiskSharing.VaRConv.distFn
      congr 2
      ext ω
      simp [hxm]
    rw [this]
  · push Not at hxm
    have h0 : TailRiskSharing.VaRConv.distFn P (fun ω => max (X ω) m) x = 0 := by
      unfold TailRiskSharing.VaRConv.distFn
      have : {ω | max (X ω) m ≤ x} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le hxm (le_max_right _ _)
      show P.real {ω | max (X ω) m ≤ x} = 0
      rw [this]; simp
    have hbdd : BddBelow {y : ℝ | 1 - ε < TailRiskSharing.VaRConv.distFn P X y} := by
      refine ⟨-C, fun y hy => ?_⟩
      by_contra hlt
      push Not at hlt
      have : TailRiskSharing.VaRConv.distFn P X y = 0 := by
        unfold TailRiskSharing.VaRConv.distFn
        have hnull : P {ω | X ω ≤ y} = 0 := by
          refine measure_mono_null (t := {ω | ¬ |X ω| ≤ C}) ?_ (ae_iff.mp hC)
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω ⊢
          intro habs
          have := (abs_le.mp habs).1
          linarith
        simp [Measure.real, hnull]
      have hy' : 1 - ε < TailRiskSharing.VaRConv.distFn P X y := hy
      rw [this] at hy'
      linarith
    have hF : TailRiskSharing.VaRConv.distFn P X x ≤ 1 - ε := by
      by_contra hgt
      push Not at hgt
      have hmem : x ∈ {y : ℝ | 1 - ε < TailRiskSharing.VaRConv.distFn P X y} := hgt
      have := csInf_le hbdd hmem
      have h2 : m ≤ x := le_trans hmR this
      linarith
    rw [h0]
    have : max (0 - (1 - ε)) 0 = 0 := by simp; linarith
    rw [this]
    have h3 : max (TailRiskSharing.VaRConv.distFn P X x - (1 - ε)) 0 = 0 := by
      simp; linarith
    rw [h3]
