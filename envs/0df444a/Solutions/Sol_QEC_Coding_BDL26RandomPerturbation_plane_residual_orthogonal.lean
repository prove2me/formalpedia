-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.plane_residual_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:04.243207+00:00
-- url     : https://prove2.me/submissions/2cb73655-114e-4233-8aa8-c2f577c990b6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_plane_coefficients
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c d : Space) (hdet : gramDet b c ≠ 0) :
    inner ℝ (d-(planeU b c d • b+planeV b c d • c)) b = 0 ∧
      inner ℝ (d-(planeU b c d • b+planeV b c d • c)) c = 0 := by
  have h := plane_coefficients b c d hdet
  simp only [inner_sub_left,inner_add_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,real_inner_comm b c]
  constructor <;> linarith
end QEC.Coding.BDL26RandomPerturbation
