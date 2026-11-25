-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuous_ptNormSq_cb0742b2cef1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:25.250286+00:00
-- url     : https://prove2.me/submissions/0d3528c0-2622-400c-8dc6-2c1a58ae371a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuousOn_source_of_chart_59202810ddfe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_of_mem_31a5af5eaaf9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hx⟩ := A.cover x
  have hsj : ContinuousOn (s j) (A.chart j).source :=
    continuousOn_source_of_chart j (hs.1 j j).continuousOn
  have hφj : ContinuousOn (W.φ j) (A.chart j).source :=
    continuousOn_source_of_chart j (W.smooth j j).continuousOn
  have hF : ContinuousOn (fun y => ‖s j y‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j y))
      (A.chart j).source :=
    ((hsj.norm.pow 2).mul ((continuousOn_const.mul hφj).rexp))
  have hopen := (A.chart j).open_source
  refine (hF.continuousAt (hopen.mem_nhds hx)).congr ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact (ptNormSq_eq_of_mem W hs j hy).symm
end GroundTheory.Heights₂.Heights.HilbertSamuel
