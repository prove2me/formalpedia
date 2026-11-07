-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.capHeight_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:53.589757+00:00
-- url     : https://prove2.me/submissions/f9db49e9-dcd7-4c99-9320-f3c2eb253bf1

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {a b : ℝ} (hab : a ≤ b) :
    capHeight a - capHeight b = max 0 (min 1 b - max (-1) a) := by
  simp only [capHeight,max_def,min_def]
  split_ifs <;> linarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap
