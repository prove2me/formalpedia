-- Prove2me | solution 1 for QFS.lintegral_jumpKernel_far
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:03:05.718159+00:00
-- url     : https://prove2.me/submissions/03bb0d7b-2ed5-4f71-882a-62bf843a3aa6

import Theorems.Thm_QFS_lintegral_compl_ball_rpow_scale



import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}



namespace QFSProof_lintegral_jumpKernel_far

theorem lintegral_compl_ball_kernel {α r : ℝ} (hr : 0 < r) :
    ∫⁻ u in {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖},
        ENNReal.ofReal (‖u‖ ^ (-(d : ℝ) - α))
      = ENNReal.ofReal (r ^ (-α)) * kernelTail d α :=
  QFS.lintegral_compl_ball_rpow_scale hr

end QFSProof_lintegral_jumpKernel_far
open QFSProof_lintegral_jumpKernel_far

set_option autoImplicit false

theorem solution {α r : ℝ} (hr : 0 < r)
    (s : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ t in {t : EuclideanSpace ℝ (Fin d) | r < ‖s - t‖}, jumpKernel d α s t
      = ENNReal.ofReal (r ^ (-α)) * kernelTail d α := by
  have hmeas : MeasurableSet {t : EuclideanSpace ℝ (Fin d) | r < ‖s - t‖} :=
    measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm
  have hmr : MeasurableSet {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hfun : ∀ t : EuclideanSpace ℝ (Fin d),
      {t : EuclideanSpace ℝ (Fin d) | r < ‖s - t‖}.indicator
          (fun t => jumpKernel d α s t) t
        = ({u : EuclideanSpace ℝ (Fin d) | r < ‖u‖}.indicator
            (fun u => ENNReal.ofReal (‖u‖ ^ (-(d : ℝ) - α)))) (s - t) := by
    intro t
    by_cases ht : r < ‖s - t‖
    · rw [Set.indicator_of_mem
        (show t ∈ {t : EuclideanSpace ℝ (Fin d) | r < ‖s - t‖} from ht),
        Set.indicator_of_mem
        (show s - t ∈ {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖} from ht), jumpKernel]
    · rw [Set.indicator_of_notMem
        (show t ∉ {t : EuclideanSpace ℝ (Fin d) | r < ‖s - t‖} from ht),
        Set.indicator_of_notMem
        (show s - t ∉ {u : EuclideanSpace ℝ (Fin d) | r < ‖u‖} from ht)]
  rw [← lintegral_indicator hmeas, ← lintegral_compl_ball_kernel (d := d) (α := α) hr,
    ← lintegral_indicator hmr]
  rw [show (fun t : EuclideanSpace ℝ (Fin d) =>
      {t : EuclideanSpace ℝ (Fin d) | r < ‖s - t‖}.indicator
        (fun t => jumpKernel d α s t) t)
      = fun t => ({u : EuclideanSpace ℝ (Fin d) | r < ‖u‖}.indicator
          (fun u => ENNReal.ofReal (‖u‖ ^ (-(d : ℝ) - α)))) (s - t) from funext hfun]
  exact lintegral_sub_left_eq_self _ s
#print axioms solution
