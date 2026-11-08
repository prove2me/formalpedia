-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPeterssonTrace_effectiveInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:19:25.270176+00:00
-- url     : https://prove2.me/submissions/12bcfe50-20be-429c-bfc6-3d51d7046a4b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_invariant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) (τ : ℍ) :
    lpsCuspPeterssonTrace N f g (h • τ) = lpsCuspPeterssonTrace N f g τ := by
  obtain ⟨h',hh'⟩ := lpsEffectiveRepresentative h
  change lpsCuspPeterssonTrace N f g ((h : Equiv.Perm ℍ) τ) = _
  rw [hh']
  exact lpsCuspPeterssonTrace_invariant N f g h' τ
end QEC.Coding.TannerLiftedProduct
