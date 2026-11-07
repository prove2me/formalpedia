-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_comp_forgetLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:34:53.646222+00:00
-- url     : https://prove2.me/submissions/58ca0f67-4686-4302-99ee-2c87c63cd586

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_preferredCuspCoordinates
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledChartMeromorphic M (dvd_trans hN hNM)
      (F ∘ lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilledChartedSpace M (dvd_trans hN hNM)
  intro x z hz
  cases x with
  | inl y =>
    have hpos : 0 < z.im :=
      lpsOriginalFilledInteriorChart_target_pos M (dvd_trans hN hNM) y z hz
    have hm := lpsOriginalFilledMeromorphicPullback_meromorphic N hN F hF z hpos
    have he : (F ∘ lpsOriginalFilledForgetLevel N M hNM) ∘
        (chartAt ℂ (Sum.inl y : LPSOriginalFilledCurve M)).symm =
        lpsOriginalFilledMeromorphicPullback N F := by
      funext q
      change F (lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledInteriorChart M (dvd_trans hN hNM) y).symm q)) = _
      rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledForgetLevel_projection]
      rfl
    rw [he]
    exact hm
  | inr c =>
    let d := lpsOriginalCuspForgetLevel N M hNM c
    let eM := lpsOriginalFilledCuspChart M c
    let eN := lpsOriginalFilledCuspChart N d
    let e := lpsOriginalCuspLevelDegree N M (lpsOriginalCuspRepresentative M c)
    obtain ⟨α,hα,hαnorm,h⟩ :=
      lpsOriginalFilledForgetLevel_preferredCuspCoordinates N M hNM c
    have htarget : α*z^e ∈ eN.target := (h z hz).1
    have hm : MeromorphicAt (F ∘ eN.symm) (α*z^e) :=
      hF (Sum.inr d) (α*z^e) htarget
    have ha : AnalyticAt ℂ (fun q : ℂ => α*q^e) z :=
      analyticAt_const.mul (analyticAt_id.pow e)
    have he : (F ∘ eN.symm) ∘ (fun q : ℂ => α*q^e) =ᶠ[𝓝 z]
        (F ∘ lpsOriginalFilledForgetLevel N M hNM) ∘ eM.symm := by
      filter_upwards [eM.open_target.mem_nhds hz] with q hq
      exact (congrArg F ((h q hq).2.1)).symm
    exact (hm.comp_analyticAt (g := fun q : ℂ => α*q^e) (x := z) ha).congr (he.filter_mono nhdsWithin_le_nhds)
end QEC.Coding.TannerLiftedProduct
