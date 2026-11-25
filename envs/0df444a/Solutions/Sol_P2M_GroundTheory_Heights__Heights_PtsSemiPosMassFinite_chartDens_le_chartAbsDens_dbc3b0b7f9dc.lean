-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_chartDens_le_chartAbsDens_dbc3b0b7f9dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:27:42.196328+00:00
-- url     : https://prove2.me/submissions/ad10bd80-c11f-4ea3-a518-a6646406c373

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSemiPosMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSegreChartFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSemiPosMassFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_finsum_le_finsum_abs_200e865e6b5f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot sheetDensity fibre mcPts segre
  maDensity cxHessian IsSheet)
open GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite
namespace GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite
theorem _root_.solution {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartDens J A f φ y ≤ chartAbsDens J A f φ y := by
  classical
  unfold chartDens chartAbsDens sheetSum
  refine (finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite
