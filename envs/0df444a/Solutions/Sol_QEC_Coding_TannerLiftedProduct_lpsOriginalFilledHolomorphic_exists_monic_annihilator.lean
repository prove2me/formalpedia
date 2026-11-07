-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledHolomorphic_exists_monic_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:57:06.832287+00:00
-- url     : https://prove2.me/submissions/0bd9cab5-8114-4f5b-9c23-a36111db6a9c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicMonicEquation_monic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicMonicEquation_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => F (Sum.inl ⟦τ⟧))) :
    ∃ Φ : Polynomial (Polynomial ℂ), Φ.Monic ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (F (Sum.inl ⟦τ⟧)) = 0 := by
  obtain ⟨k,hk⟩ := lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded N hN F hF
  let A := lpsOriginalFilledFunctionDeltaModularForm N F k hhol hk
  exact ⟨lpsOriginalHolomorphicMonicEquation N k A,lpsOriginalHolomorphicMonicEquation_monic N k A,
    lpsOriginalHolomorphicMonicEquation_root N k A (fun τ => F (Sum.inl ⟦τ⟧)) (fun _ => rfl)⟩
end QEC.Coding.TannerLiftedProduct
