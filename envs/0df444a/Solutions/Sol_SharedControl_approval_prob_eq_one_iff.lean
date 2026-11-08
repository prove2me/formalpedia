-- Prove2me | solution 1 for SharedControl.approval_prob_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:46:23.283086+00:00
-- url     : https://prove2.me/submissions/b4844d8e-4c98-4483-9e99-f0fbca168b2e

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Standing

open MeasureTheory

open SharedControl in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hM : Standing M) (t : ℝ) :
    M.P {ω | t ≤ M.πg + M.r ω} = 1 ↔ t ≤ M.πg + M.rl := by
  haveI := hM.isProbabilityMeasure
  have hmeas : MeasurableSet {ω | t ≤ M.πg + M.r ω} :=
    measurableSet_le measurable_const (measurable_const.add hM.measurable_r)
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hpos := hM.rl_min_support (t - M.πg - M.rl) (by linarith)
    have hc : M.P {ω | t ≤ M.πg + M.r ω}ᶜ = 0 := (prob_compl_eq_zero_iff hmeas).mpr h
    have hsub : {ω | M.r ω < M.rl + (t - M.πg - M.rl)} ⊆ {ω | t ≤ M.πg + M.r ω}ᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hω ⊢
      intro h'
      linarith
    have h0 := measure_mono_null hsub hc
    rw [h0] at hpos
    exact lt_irrefl _ hpos
  · intro h
    rw [← prob_compl_eq_zero_iff hmeas]
    have hae := hM.ae_mem_Icc
    rw [ae_iff] at hae
    apply measure_mono_null _ hae
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hω ⊢
    intro hI
    exact hω (by linarith [hI.1])
