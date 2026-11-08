-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:52:36.29241+00:00
-- url     : https://prove2.me/submissions/cd01f748-b93b-410a-b924-70dee823de0a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup) (hr : ∀c, QuotientGroup.mk (r c) = c) (τ : ℍ) :
    ∃h : H,h • τ ∈ lpsCosetSectionDomain H r := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  let g' : lpsEffectiveModularGroup := (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict g
  let c : lpsEffectiveModularGroup ⧸ H := QuotientGroup.mk g'
  have hc : QuotientGroup.mk (r c) = QuotientGroup.mk g' := hr c
  have hk : (r c)⁻¹*g' ∈ H := QuotientGroup.eq.mp hc
  let h : H := ⟨(r c)⁻¹*g',hk⟩
  refine ⟨h,Set.mem_iUnion.mpr ⟨c,?_⟩⟩
  rw [mem_smul_set_iff_inv_smul_mem]
  change (r c) • (((r c)⁻¹*g') • τ) ∈ ModularGroup.fd
  rw [←mul_smul,mul_inv_cancel_left]
  change g • τ ∈ ModularGroup.fd
  exact hg
end QEC.Coding.TannerLiftedProduct
