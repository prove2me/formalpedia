-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.master_output_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:36:01.001536+00:00
-- url     : https://prove2.me/submissions/71f3b85b-9d72-4253-b816-3d4bf3b0b9e8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_counters_original
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_haltTime_original

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
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) :
    output (masterSupport P) (masterBad P r lambda K J) T =
      output (eventSupport P J r) (eventBad P J r lambda K) T := by
  unfold output
  rw [master_haltTime_original, master_counters_original]
end QEC.Coding.BDL26RandomPerturbation
