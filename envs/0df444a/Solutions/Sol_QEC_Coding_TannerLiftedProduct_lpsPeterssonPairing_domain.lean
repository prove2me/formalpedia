-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPeterssonPairing_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:23:50.542963+00:00
-- url     : https://prove2.me/submissions/c07c8e7d-5bfd-4df1-814a-339ff3776c75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPeterssonTrace_effectiveInvariant
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
    lpsCuspPeterssonPairing N f g = ∫τ in s,lpsCuspPeterssonTrace N f g τ :=
  lpsEffectiveFundamentalDomain.setIntegral_eq hs (lpsPeterssonTrace_effectiveInvariant N f g)
end QEC.Coding.TannerLiftedProduct
