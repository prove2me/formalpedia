-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.measurable_pulledOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:50:54.326631+00:00
-- url     : https://prove2.me/submissions/f977a267-175c-4b02-a6e4-a7722e8ce199

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_eventBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurableSet_codedBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_output


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26DecodingGraph
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
variable {A : Type*} [Fintype A] [DecidableEq A]
namespace QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) :
    Measurable (pulledOutput P J r lambda K u) :=
  measurable_output (X := fun _ : A => Space) _ _ (measurableSet_codedBad u _ _ (measurableSet_eventBad P J r lambda K))
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
