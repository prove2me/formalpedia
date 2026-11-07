-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCurve_finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:07.80292+00:00
-- url     : https://prove2.me/submissions/9569731d-6af3-4600-92b1-009d5424447c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspClosedPatch_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspClosedPatch_high_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGamma0Projected_fundamentalDomain_cover


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    (Sum.inl '' lpsOriginalGamma0CompactCore N 2) ∪
      (⋃ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        lpsOriginalFilledCuspClosedPatch N c)=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  cases x with
  | inl y =>
    obtain ⟨τ,rfl⟩ := Quotient.exists_rep y
    obtain ⟨c,z,hz,he⟩ := lpsOriginalGamma0Projected_fundamentalDomain_cover N τ
    by_cases h : z.im≤2
    · left
      refine ⟨⟦τ⟧,?_,rfl⟩
      rw [←he]
      exact Set.mem_iUnion.mpr ⟨c,z,⟨hz,h⟩,rfl⟩
    · right
      have hh : 1<z.im := by linarith
      have hi := lpsOriginalFilledCuspClosedPatch_high_projection N
        (lpsOriginalGamma0CosetRepresentative N c) ⟨z,hh⟩ (le_of_lt (lt_of_not_ge h))
      change Sum.inl (lpsOriginalGamma0Projected N
        (lpsOriginalGamma0CosetRepresentative N c) z)∈_ at hi
      rw [he] at hi
      exact Set.mem_iUnion.mpr ⟨_,hi⟩
  | inr c =>
    exact Or.inr (Set.mem_iUnion.mpr ⟨c,lpsOriginalFilledCuspClosedPatch_cusp N c⟩)
end QEC.Coding.TannerLiftedProduct
