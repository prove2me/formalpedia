-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_polynomial_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:09:18.161204+00:00
-- url     : https://prove2.me/submissions/306a202b-986a-4b25-8088-dd3a615fcf36

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_constant_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_polynomial_eval


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLocalChartGermTopology
variable (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_125
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_131
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_132
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_133
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_135
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_136
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (p : P) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K p) := by
  let φ : P →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ P K
  have he : p.eval₂ (algebraMap ℂ K) (algebraMap P K Polynomial.X) =
      algebraMap P K p := Polynomial.eval₂_algebraMap_X p φ
  rw [← he]
  exact nonnegative_polynomial_eval (lpsOriginalFieldLocalOrder N hN hpos x)
    (algebraMap ℂ K) (lpsOriginalFieldLocalOrder_constant_nonnegative N hN hpos x)
    _ hj p
end QEC.Coding.TannerLiftedProduct
