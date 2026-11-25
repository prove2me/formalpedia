-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.MpE.eventually_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:57.253011+00:00
-- url     : https://prove2.me/submissions/43270fe9-6281-4da7-97fc-db62bdf2b041

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticGroupT2Space
import Theorems.Thm_P2M_PositivityTheory_ThKR_Mp_MpE_toBlocks___one__9b58d089797c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.MpE
namespace PositivityTheory.ThKR.Mp.MpE
theorem _root_.solution : ∀ᶠ s in 𝓝 (1 : Sp l), 0 < s.1.toBlocks₁₁.det := by
  have hc : Continuous fun s : Sp l => s.1.toBlocks₁₁.det :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
      continuous_subtype_val.matrix_elem (Sum.inl i) (Sum.inl j))
  have h1 : (1 : Sp l).1.toBlocks₁₁.det = 1 := by
    rw [show (1 : Sp l).1 = 1 from rfl, toBlocks₁₁_one', Matrix.det_one]
  have h2 : ∀ᶠ y in 𝓝 ((1 : Sp l).1.toBlocks₁₁.det), (0 : ℝ) < y := lt_mem_nhds (by rw [h1]; exact one_pos)
  exact (hc.tendsto 1).eventually h2
end PositivityTheory.ThKR.Mp.MpE
