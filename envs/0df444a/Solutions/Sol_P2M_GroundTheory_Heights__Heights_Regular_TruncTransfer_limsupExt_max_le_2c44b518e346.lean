-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_limsupExt_max_le_2c44b518e346
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:34.053335+00:00
-- url     : https://prove2.me/submissions/b1fb105a-7b25-4977-85de-0f050afbd3e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_nebot_diff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.TruncTransfer
namespace GroundTheory.Heights₂.Heights.Regular.TruncTransfer
theorem _root_.solution {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) (S : Finset (Fin D))
    (v : (Fin D → ℂ) → ℝ) (K c r : ℝ) {y : Fin D → ℂ} (hy : y ∈ U) (hr : 0 < r)
    (h : ∀ y' ∈ ball y r, y' ∈ U → y' ∉ coordDiv S → max (v y') (-K) ≤ c) :
    limsupExt U (coordDiv S) (fun y' => max (v y') (-K)) y ≤ c := by
  unfold limsupExt
  split_ifs with hyS
  · have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S) hU hy
    refine limsup_le_of_le (isCoboundedUnder_le_of_le _ fun _ => le_max_right _ (-K)) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds y hr)] with y' hy' hb
    exact h y' hb hy'.1 hy'.2
  · exact h y (mem_ball_self hr) hy hyS
end GroundTheory.Heights₂.Heights.Regular.TruncTransfer
