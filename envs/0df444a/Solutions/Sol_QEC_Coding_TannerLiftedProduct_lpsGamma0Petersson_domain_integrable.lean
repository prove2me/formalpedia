-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_domain_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:47:58.048183+00:00
-- url     : https://prove2.me/submissions/0a8e1d17-8524-4279-8285-fafbd9a87b79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Petersson_effectiveInvariant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_integrable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IntegrableOn (petersson 2 f g) s volume :=
  ((lpsGamma0PeterssonDomain_fundamental N).integrableOn_iff hs
    (lpsGamma0Petersson_effectiveInvariant N f g)).mp (lpsGamma0PeterssonDomain_integrable N f g)
end QEC.Coding.TannerLiftedProduct
