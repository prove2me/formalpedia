-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPeterssonPairing_translatedDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:17.174457+00:00
-- url     : https://prove2.me/submissions/17576f6e-db86-4f2e-92c2-26e378407dd7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPeterssonPairing_domain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) :
    lpsCuspPeterssonPairing N f g = ∫τ in h • ModularGroup.fd,lpsCuspPeterssonTrace N f g τ :=
  lpsPeterssonPairing_domain N f g (lpsEffectiveFundamentalDomain.smul h)
end QEC.Coding.TannerLiftedProduct
