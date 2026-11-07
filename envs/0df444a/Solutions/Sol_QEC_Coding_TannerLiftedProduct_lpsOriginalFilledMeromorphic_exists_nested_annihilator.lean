-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_nested_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:54:08.381827+00:00
-- url     : https://prove2.me/submissions/03ae22da-a30b-4612-844b-bf62eda9988a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_nonzero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_modular_ratio


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ ≠ 0 ∧
      Φ.natDegree ≤ Nat.card (LPSOriginalMeromorphicCosets N) ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (F (Sum.inl ⟦τ⟧)) = 0 := by
  obtain ⟨k,A,B,hB,hAB⟩ := lpsOriginalFilledMeromorphic_exists_modular_ratio N hN F hF
  exact ⟨lpsOriginalMeromorphicRatioEquation N k A B,
    lpsOriginalMeromorphicRatioEquation_nonzero N k A B hB,
    lpsOriginalMeromorphicRatioEquation_degree N k A B,
    lpsOriginalMeromorphicRatioEquation_root N k A B _ hAB⟩
end QEC.Coding.TannerLiftedProduct
