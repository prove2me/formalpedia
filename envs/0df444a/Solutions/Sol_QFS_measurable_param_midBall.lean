-- Prove2me | solution 1 for QFS.measurable_param_midBall
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:06.279123+00:00
-- url     : https://prove2.me/submissions/5d10bf54-15ac-4b6d-9b9e-3d6a383a0690




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

theorem solution {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (ϑ : ℝ)
    {H : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hH : Measurable H) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖, H (p, z) := by
  have hset : MeasurableSet {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin d) | q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖} := by
    have h1 : Continuous fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) => dist q.2 (midCentre v ϑ q.1.1 q.1.2) := by
      unfold midCentre; fun_prop
    have h2 : Continuous fun q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
        EuclideanSpace ℝ (Fin d) => ‖q.1.1 - q.1.2‖ := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le h1 h2).measurableSet
  have heq : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ∫⁻ z in closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖, H (p, z))
      = fun p => ∫⁻ z, {q : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          EuclideanSpace ℝ (Fin d) |
          q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖}.indicator H (p, z) := by
    funext p
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ closedBall (midCentre v ϑ p.1 p.2) ‖p.1 - p.2‖
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show (p, z) ∈ {q :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
      q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖} from hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show (p, z) ∉ {q :
        (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) |
        q.2 ∈ closedBall (midCentre v ϑ q.1.1 q.1.2) ‖q.1.1 - q.1.2‖} from hz)]
  rw [heq]
  exact (hH.indicator hset).lintegral_prod_right'
#print axioms solution
