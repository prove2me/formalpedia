-- Prove2me | solution 1 for QFS.norm_sub_le_of_mem_midBall
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:05.42147+00:00
-- url     : https://prove2.me/submissions/e60476a8-648e-4ff0-952b-eca0279b8495




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
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_BeyondThePaper
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


set_option autoImplicit false

theorem solution {v : E} (hv : ‖v‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ)
    (hϑ' : ϑ ≤ π / 2) {s t z : E}
    (hz : z ∈ closedBall (midCentre v ϑ s t) ‖s - t‖) :
    ‖z - s‖ ≤ (1 + 3 / Real.sin ϑ) * ‖s - t‖ ∧
      ‖z - t‖ ≤ (2 + 3 / Real.sin ϑ) * ‖s - t‖ := by
  have hsin : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hlam : 0 ≤ 3 * ‖s - t‖ / Real.sin ϑ := by positivity
  rw [Metric.mem_closedBall, dist_eq_norm, midCentre] at hz
  set q : E := z - (s + (3 * ‖s - t‖ / Real.sin ϑ) • v) with hqdef
  have hzs : z - s = q + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hzt : z - t = (q + (s - t)) + (3 * ‖s - t‖ / Real.sin ϑ) • v := by rw [hqdef]; abel
  have hq' : ‖q + (s - t)‖ ≤ 2 * ‖s - t‖ := le_trans (norm_add_le _ _) (by linarith)
  have hsmul : ‖(3 * ‖s - t‖ / Real.sin ϑ) • v‖ = 3 / Real.sin ϑ * ‖s - t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam, hv, mul_one]; ring
  constructor
  · rw [hzs]
    refine le_trans (norm_add_le _ _) ?_
    rw [hsmul]; linarith
  · rw [hzt]
    refine le_trans (norm_add_le _ _) ?_
    rw [hsmul]; linarith
#print axioms solution
