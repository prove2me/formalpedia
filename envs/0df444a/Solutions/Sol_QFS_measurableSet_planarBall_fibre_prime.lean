-- Prove2me | solution 1 for QFS.measurableSet_planarBall_fibre_prime
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:03.953135+00:00
-- url     : https://prove2.me/submissions/9ac4ae25-ff4e-4aae-8eac-04271950ea36




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

theorem solution {vs vt : EuclideanSpace ℝ (Fin 2)} (ϑ : ℝ)
    (t z : EuclideanSpace ℝ (Fin 2)) :
    MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t} := by
  have h1 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | s ≠ t} := by
    have he : {s : EuclideanSpace ℝ (Fin 2) | s ≠ t}
        = ({t} : Set (EuclideanSpace ℝ (Fin 2)))ᶜ := by
      ext s; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq]
    rw [he]; exact (measurableSet_singleton t).compl
  have h2 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} :=
    ((isOpen_doubleCone vs ϑ).preimage (by fun_prop)).measurableSet.compl
  have h3 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ} :=
    ((isOpen_doubleCone vt ϑ).preimage (by fun_prop)).measurableSet.compl
  have h4 : MeasurableSet {s : EuclideanSpace ℝ (Fin 2) |
      z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    have hc1 : Continuous fun s : EuclideanSpace ℝ (Fin 2) =>
        dist z (planarCtr vs vt s t) := by unfold planarCtr planarA cross2; fun_prop
    have hc2 : Continuous fun s : EuclideanSpace ℝ (Fin 2) =>
        ‖t - s‖ * Real.sin ϑ ^ 2 / 2 := by fun_prop
    simpa [Metric.mem_closedBall] using (isClosed_le hc1 hc2).measurableSet
  have hEq : {s : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s t}
      = ({s : EuclideanSpace ℝ (Fin 2) | s ≠ t} ∩
          {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vs ϑ} ∩
          {s : EuclideanSpace ℝ (Fin 2) | t - s ∉ doubleCone vt ϑ}) ∩
        {s : EuclideanSpace ℝ (Fin 2) |
          z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)} := by
    ext s
    simp only [planarBall, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hEq]
  exact ((h1.inter h2).inter h3).inter h4
#print axioms solution
