-- Prove2me | solution 1 for QFS.measurableSet_planarBall
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:03.286992+00:00
-- url     : https://prove2.me/submissions/793fadba-17ef-4382-917a-c3dd18ee32a4




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
    (s t : EuclideanSpace ℝ (Fin 2)) : MeasurableSet (planarBall vs vt ϑ s t) := by
  by_cases hP : s ≠ t ∧ t - s ∉ doubleCone vs ϑ ∧ t - s ∉ doubleCone vt ϑ
  · have he : planarBall vs vt ϑ s t
        = closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2) := by
      ext z
      simp only [planarBall, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2.2.2, fun h => ⟨hP.1, hP.2.1, hP.2.2, h⟩⟩
    rw [he]; exact measurableSet_closedBall
  · have he : planarBall vs vt ϑ s t = ∅ := by
      ext z
      simp only [planarBall, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hP ⟨h.1, h.2.1, h.2.2.1⟩
    rw [he]; exact MeasurableSet.empty
#print axioms solution
