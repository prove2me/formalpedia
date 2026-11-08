-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:29:23.866044+00:00
-- url     : https://prove2.me/submissions/2a8bbbe2-7c82-4e02-8658-ca2c09808d9a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold ContDiff TensorProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_28
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_35
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_36
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_37
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_70
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_74
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X)) =
        lpsOriginalCompactMeromorphicCovectorClass N hN
          ⟨lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N),
            lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
              (lpsOriginalFilledChartMeromorphic_j N hN)⟩ :=
  lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D N hpos hN
    (algebraMap P K Polynomial.X) ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j N hpos hN).symm
end QEC.Coding.TannerLiftedProduct
