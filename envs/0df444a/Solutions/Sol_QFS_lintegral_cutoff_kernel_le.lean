-- Prove2me | solution 1 for QFS.lintegral_cutoff_kernel_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:06.96148+00:00
-- url     : https://prove2.me/submissions/fd6ff638-0076-48b1-a487-9bd85c77015c




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


set_option autoImplicit false

theorem solution {Γ : Configuration (EuclideanSpace ℝ (Fin d))}
    {α Λ : ℝ} {k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hk : KernelBounds Γ α Λ k) {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ y, ENNReal.ofReal (min (‖x - y‖ ^ 2 / δ ^ 2) 1) * k x y
      ≤ ENNReal.ofReal Λ *
        ∫⁻ u : EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)) := by
  have hΛ : (0 : ℝ) ≤ Λ := le_trans zero_le_one hk.one_le
  have hFm : Measurable fun u : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)) := by fun_prop
  calc ∫⁻ y, ENNReal.ofReal (min (‖x - y‖ ^ 2 / δ ^ 2) 1) * k x y
      ≤ ∫⁻ y, ENNReal.ofReal (min (‖x - y‖ ^ 2 / δ ^ 2) 1) *
          (ENNReal.ofReal Λ * jumpKernel d α x y) :=
        lintegral_mono fun y => mul_le_mul' le_rfl (hk.upper x y)
    _ = ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (min (‖y - x‖ ^ 2 / δ ^ 2) 1 *
          ‖y - x‖ ^ (-(d : ℝ) - α)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        rw [jumpKernel, norm_sub_rev x y,
          ENNReal.ofReal_mul (le_min (by positivity) zero_le_one)]
        ring
    _ = ENNReal.ofReal Λ * ∫⁻ u : EuclideanSpace ℝ (Fin d),
          ENNReal.ofReal (min (‖u‖ ^ 2 / δ ^ 2) 1 * ‖u‖ ^ (-(d : ℝ) - α)) := by
        congr 1
        exact (measurePreserving_sub_right volume x).lintegral_comp hFm
#print axioms solution
