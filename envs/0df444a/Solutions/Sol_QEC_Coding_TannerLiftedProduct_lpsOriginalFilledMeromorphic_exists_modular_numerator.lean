-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_exists_modular_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:35.176538+00:00
-- url     : https://prove2.me/submissions/e711056c-1130-4125-9c39-9faec5201269

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    ∃ (P : Polynomial ℂ) (k : ℕ)
      (A : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        ((k : ℤ)*12)), P.Monic ∧ ∀ τ : ℍ,
      A τ = ModularForm.discriminant τ ^ k *
        P.eval (lpsOriginalJInvariant τ) * F (Sum.inl ⟦τ⟧) := by
  obtain ⟨P,hP,hhol⟩ :=
    lpsOriginalFilledMeromorphic_exists_holomorphic_pole_clearing N hN F hF
  let G : LPSOriginalFilledCurve N → ℂ := fun x =>
    P.eval (lpsOriginalFilledJ N x) * F x
  have hG : lpsOriginalFilledChartMeromorphic N hN G :=
    lpsOriginalFilledChartMeromorphic_mul N hN
      (lpsOriginalFilledChartMeromorphic_polynomial N hN
        (lpsOriginalFilledChartMeromorphic_j N hN) P) hF
  obtain ⟨k,hk⟩ := lpsOriginalFilledMeromorphic_exists_delta_cusp_bounded N hN G hG
  let A := lpsOriginalFilledFunctionDeltaModularForm N G k hhol hk
  refine ⟨P,k,A,hP,?_⟩
  intro τ
  change ModularForm.discriminant τ ^ k *
    (P.eval (lpsOriginalFilledJ N (Sum.inl ⟦τ⟧)) * F (Sum.inl ⟦τ⟧)) = _
  rw [lpsOriginalFilledJ_projection,mul_assoc]
end QEC.Coding.TannerLiftedProduct
