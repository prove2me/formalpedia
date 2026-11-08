-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlashPetersson_right_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:07:03.05294+00:00
-- url     : https://prove2.me/submissions/27456b17-3a35-4e4a-9a3a-4e860ca60d9d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlashPetersson_bounded
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_volume_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    IntegrableOn (petersson 2 f (g ∣[(2:ℤ)] A)) (lpsGamma0PeterssonDomain N) volume := by
  obtain ⟨C,hC⟩ := lpsWeightTwoSlashPetersson_bounded N g f A hA
  have hi : IntegrableOn (fun _ : ℍ => C) (lpsGamma0PeterssonDomain N) :=
    integrableOn_const (ne_of_lt (lpsGamma0PeterssonDomain_volume_finite N))
  have hc : Continuous (g ∣[(2:ℤ)] A) := (g.holo'.slash 2 A).continuous
  apply hi.mono' (petersson_continuous 2 (by fun_prop) hc).aestronglyMeasurable
  exact Eventually.of_forall fun τ => by rw [petersson_norm_symm];exact hC τ
end QEC.Coding.TannerLiftedProduct
