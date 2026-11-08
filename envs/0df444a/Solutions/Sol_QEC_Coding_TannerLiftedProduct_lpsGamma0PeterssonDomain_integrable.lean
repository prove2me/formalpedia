-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:55:17.683195+00:00
-- url     : https://prove2.me/submissions/bce9f380-ac11-4ea3-bf10-507cd9ee48aa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Petersson_translate_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Domain_finiteIndex


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (petersson 2 f g) (lpsGamma0PeterssonDomain N) volume := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  let : Fintype (lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact integrableOn_finite_iUnion.mpr (fun c => lpsGamma0Petersson_translate_integrable N f g _)
end QEC.Coding.TannerLiftedProduct
