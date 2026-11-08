-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_translate_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:53:51.631198+00:00
-- url     : https://prove2.me/submissions/1fbaa877-97ed-45a1-a9a1-cb2ef765790d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_fundamentalDomain_volume_finite


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) :
    IntegrableOn (petersson 2 f g) (h • ModularGroup.fd) volume := by
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left 2 _ f g
  have hi : IntegrableOn (fun _ : ℍ => C) (h • ModularGroup.fd) := by
    have ht : (volume : Measure ℍ) (h • ModularGroup.fd) ≠ ∞ := by
      rw [measure_smul]
      exact ne_of_lt lpsPetersson_fundamentalDomain_volume_finite
    exact integrableOn_const ht
  exact hi.mono' (petersson_continuous 2 (by fun_prop) (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall hC)
end QEC.Coding.TannerLiftedProduct
