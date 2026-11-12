-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowPhysicalSuccessor_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:34:37.999676+00:00
-- url     : https://prove2.me/submissions/b357a938-c68f-420c-8742-6fb7074acb5a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowPerturbationOutput_value

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26IncomingRowsExecution
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    rowPhysicalSuccessor p n J T=physicalSuccessorOutput p n J T := by
  exact congrArg
    (replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n))
    (rowPerturbationOutput_value p n J T)
end QEC.Coding.BDL26IncomingRowsExecution
