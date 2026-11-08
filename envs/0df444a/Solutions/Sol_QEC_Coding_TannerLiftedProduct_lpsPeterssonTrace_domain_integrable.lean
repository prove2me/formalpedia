-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPeterssonTrace_domain_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:13.731327+00:00
-- url     : https://prove2.me/submissions/5c12206f-1aa4-43a2-aae1-c19206c3af20

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPeterssonTrace_effectiveInvariant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain lpsEffectiveModularGroup s volume) :
    IntegrableOn (lpsCuspPeterssonTrace N f g) s volume :=
  (lpsEffectiveFundamentalDomain.integrableOn_iff hs
    (lpsPeterssonTrace_effectiveInvariant N f g)).mp (lpsCuspPeterssonTrace_integrable N f g)
end QEC.Coding.TannerLiftedProduct
