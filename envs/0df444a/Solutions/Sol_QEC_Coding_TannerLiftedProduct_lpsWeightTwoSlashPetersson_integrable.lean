-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlashPetersson_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:06:41.372206+00:00
-- url     : https://prove2.me/submissions/7e7e2090-419a-4d51-98ca-42566a1e536d

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
    IntegrableOn (petersson 2 (f ∣[(2:ℤ)] A) g) (lpsGamma0PeterssonDomain N) volume := by
  obtain ⟨C,hC⟩ := lpsWeightTwoSlashPetersson_bounded N f g A hA
  have hi : IntegrableOn (fun _ : ℍ => C) (lpsGamma0PeterssonDomain N) :=
    integrableOn_const (ne_of_lt (lpsGamma0PeterssonDomain_volume_finite N))
  have hc : Continuous (f ∣[(2:ℤ)] A) := (f.holo'.slash 2 A).continuous
  exact hi.mono' (petersson_continuous 2 hc (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall hC)
end QEC.Coding.TannerLiftedProduct
