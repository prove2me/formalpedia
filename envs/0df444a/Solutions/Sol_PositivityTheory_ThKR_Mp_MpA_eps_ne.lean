-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpA.eps_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:29.824937+00:00
-- url     : https://prove2.me/submissions/6ce32607-4d6c-4862-b7a1-913df560f790

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
import Theorems.Thm_PositivityTheory_ThKR_Mp_MpA_omS_eps
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
import Theorems.Thm_PositivityTheory_ThKF_E_exists_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpA
namespace PositivityTheory.ThKR.Mp.MpA
theorem _root_.solution : (eps : G l) ≠ 1 := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have h1 : omS (eps : G l) φ = omS (1 : G l) φ := by rw [h]
  rw [omS_eps, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 : -φ 0 = φ 0 := by
    have := congrArg (fun u : Sch l => u 0) h1
    simpa using this
  exact hφ (by linear_combination (-1 / 2 : ℂ) * h2)
end PositivityTheory.ThKR.Mp.MpA
