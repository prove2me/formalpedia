-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.cap_opposite_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:38.919856+00:00
-- url     : https://prove2.me/submissions/2173f962-066d-4440-a565-6175d0763a3f

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
    cap u c ∩ cap (opposite u) (-c) =
      {s : Sphere | inner ℝ (u : Space) (s : Space) = c} := by
  ext s
  simp only [cap,opposite,mem_inter_iff,mem_setOf_eq,inner_neg_left]
  constructor
  · rintro ⟨h1,h2⟩
    linarith
  · intro h
    constructor <;> linarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap
