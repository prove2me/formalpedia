-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_cap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:51:21.330937+00:00
-- url     : https://prove2.me/submissions/72dc3f69-a482-43ca-bc0c-d5749f4748df

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) {c : ℝ} (hc : c < 1) :
    area (cap u c) ≠ 0 := by
  have ho : IsOpen {s : Sphere | c < inner ℝ (u : Space) (s : Space)} :=
    isOpen_lt continuous_const (by fun_prop)
  have hn : ({s : Sphere | c < inner ℝ (u : Space) (s : Space)} : Set Sphere).Nonempty := by
    refine ⟨u, ?_⟩
    simpa only [mem_setOf_eq, real_inner_self_eq_norm_sq, norm_coe, one_pow] using hc
  have hsub : {s : Sphere | c < inner ℝ (u : Space) (s : Space)} ⊆ cap u c := by
    intro s hs
    change c ≤ inner ℝ (u : Space) (s : Space)
    exact hs.le
  exact ne_of_gt ((ho.measure_pos area hn).trans_le (measure_mono hsub))
end QEC.Coding.ProbabilisticConstruction.SphericalCap
