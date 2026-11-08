-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNativeCovectorToLocal_agrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:32:11.093259+00:00
-- url     : https://prove2.me/submissions/3e166e6f-9378-4d8b-8d43-a07fe9ef843f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeCovectorToLocal_class
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCovectorRepresentativeToLocal_D
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCovectorRepresentativeToLocal_functionTimes
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalDifferentialMap_D
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_representative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericKaehler_expand


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "Cov" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_28
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_142
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_148
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_149
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_150
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_151
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_152
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_156
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_158
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_160
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_162
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_163
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_164
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalNativeCovectorToLocal N hN x
      (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) =
      lpsOriginalFieldLocalDifferentialMap N hpos hN x differentialForm := by
  let c : K := lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm
  let dj : KaehlerDifferential ℂ K := KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X)
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN c)
  have hFc : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN c := hF
  let σ : Cov := ⟨lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N),
    lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
      (lpsOriginalFilledChartMeromorphic_j N hN)⟩
  have hσ : lpsOriginalCompactMeromorphicCovectorClass N hN σ =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN dj :=
    (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D_j N hpos hN).symm
  have hσlocal : lpsOriginalCovectorRepresentativeToLocal N hN x σ =
      germDerivative a (lpsOriginalRepresentativeToLocal N hN x
        ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩) :=
    lpsOriginalCovectorRepresentativeToLocal_D N hN x
      ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩
  have hdifferentialForm : differentialForm = c • dj := lpsOriginalGenericKaehler_expand N hpos differentialForm
  rw [hdifferentialForm,lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
    N hpos hN c dj F σ hFc hσ,lpsOriginalNativeCovectorToLocal_class,
    lpsOriginalCovectorRepresentativeToLocal_functionTimes,
    ← lpsOriginalFieldToLocal_representative N hN hpos x c F hFc]
  change lpsOriginalFieldToLocal N hN hpos x c *
    lpsOriginalCovectorRepresentativeToLocal N hN x σ = _
  rw [hσlocal,← lpsOriginalFieldToLocal_j N hN hpos x]
  change lpsOriginalFieldToLocal N hN hpos x c *
    germDerivative a (lpsOriginalFieldToLocal N hN hpos x (algebraMap P K Polynomial.X)) =
      lpsOriginalFieldLocalDifferentialMap N hpos hN x
        (c • KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X))
  rw [map_smul,lpsOriginalFieldLocalDifferentialMap_D]
  rfl
end QEC.Coding.TannerLiftedProduct
