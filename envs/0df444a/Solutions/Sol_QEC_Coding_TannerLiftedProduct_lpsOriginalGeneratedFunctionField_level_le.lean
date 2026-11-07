-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:42:40.751306+00:00
-- url     : https://prove2.me/submissions/f850f4b1-ced3-46e0-b00c-96ae71bbfc9a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphicRestrictionSubfield_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFullMeromorphicEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hposN ≤ lpsOriginalGeneratedFunctionField M hposM := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  intro x hx
  have hn : lpsOriginalHolomorphicFractionToMeromorphicGerm x ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN :=
    lpsOriginalGeneratedFunctionField_mem_full_meromorphic N hposN hN ⟨x,hx⟩
  have hm : lpsOriginalHolomorphicFractionToMeromorphicGerm x ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield M (dvd_trans hN hNM) :=
    (lpsOriginalFilledMeromorphicRestrictionSubfield_level_le N M hNM hN) hn
  let A : lpsOriginalFilledMeromorphicRestrictionSubfield M (dvd_trans hN hNM) :=
    ⟨lpsOriginalHolomorphicFractionToMeromorphicGerm x,hm⟩
  let e := lpsOriginalGeneratedFullMeromorphicEquiv M hposM (dvd_trans hN hNM)
  let z : lpsOriginalGeneratedFunctionField M hposM := e.symm A
  have hz : lpsOriginalHolomorphicFractionToMeromorphicGerm z.val =
      lpsOriginalHolomorphicFractionToMeromorphicGerm x := by
    have he := congrArg Subtype.val (e.apply_symm_apply A)
    change (lpsOriginalGeneratedFullMeromorphicEquiv M hposM
      (dvd_trans hN hNM) z).val = lpsOriginalHolomorphicFractionToMeromorphicGerm x at he
    rw [lpsOriginalGeneratedFullMeromorphicEquiv_apply] at he
    exact he
  have he : z.val = x := lpsOriginalHolomorphicFractionToMeromorphicGerm_injective hz
  rw [←he]
  exact z.property
end QEC.Coding.TannerLiftedProduct
