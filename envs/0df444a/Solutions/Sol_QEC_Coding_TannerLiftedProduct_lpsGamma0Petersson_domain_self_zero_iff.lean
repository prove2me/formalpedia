-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_domain_self_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:48:00.024098+00:00
-- url     : https://prove2.me/submissions/de4cfae8-a9f2-490e-ba5b-35585b82d3c8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_gamma0Domain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    (∫τ in s,petersson 2 f f τ) = 0 ↔ f = 0 := by
  rw [←lpsCuspPeterssonPairing_gamma0Domain N f f hs]
  exact lpsCuspPeterssonPairing_self_eq_zero_iff N f
end QEC.Coding.TannerLiftedProduct
