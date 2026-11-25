-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpA.sp_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:42.18967+00:00
-- url     : https://prove2.me/submissions/e0bfa01b-d150-42f1-882f-47565255fabd

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousTo
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpA
namespace PositivityTheory.ThKR.Mp.MpA
theorem _root_.solution {X : Type} [TopologicalSpace X] {a : X → Sp l} (ha : Continuous a) :
    Continuous fun x => (a x)⁻¹ := by
  refine continuous_induced_rng.2 ?_
  show Continuous fun x => -Matrix.J l ℝ * ((a x : Mat l))ᵀ * Matrix.J l ℝ
  exact (continuous_const.mul (continuous_subtype_val.comp ha).matrix_transpose).mul continuous_const
end PositivityTheory.ThKR.Mp.MpA
