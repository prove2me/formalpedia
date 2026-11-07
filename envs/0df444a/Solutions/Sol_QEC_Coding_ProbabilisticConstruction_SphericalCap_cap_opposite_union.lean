-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.cap_opposite_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:37.905619+00:00
-- url     : https://prove2.me/submissions/98a1ebd2-7497-4f37-aa00-ff2a5c79675e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_LevelSets
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    cap u c ∪ cap (opposite u) (-c) = univ := by
  ext s
  simp only [cap,opposite,mem_union,mem_setOf_eq,inner_neg_left,mem_univ,iff_true]
  rcases le_total c (inner ℝ (u : Space) (s : Space)) with h | h
  · exact Or.inl h
  · exact Or.inr (neg_le_neg h)
end QEC.Coding.ProbabilisticConstruction.SphericalCap
