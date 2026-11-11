-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.master_counters_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:12:10.824429+00:00
-- url     : https://prove2.me/submissions/e265195d-c9e2-4260-928b-c45cf330b28f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_step_original

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    counters (masterSupport P) (masterBad P r lambda K J) T n =
      counters (eventSupport P J r) (eventBad P J r lambda K) T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [counters, counters, ih]
      exact master_step_original P J r lambda K T _
end QEC.Coding.BDL26RandomPerturbation
