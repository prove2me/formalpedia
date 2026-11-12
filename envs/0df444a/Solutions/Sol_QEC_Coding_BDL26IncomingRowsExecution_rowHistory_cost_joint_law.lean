-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.rowHistory_cost_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:30:56.790005+00:00
-- url     : https://prove2.me/submissions/b9203a3e-b323-4046-bdf9-a02bee1f8012

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowHistory_value

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (experimentLaw p N).map (fun z => (rowHistory p N z,(fun i => rowStageCost p N i z),rowTotalCost p N z))=
      (experimentLaw p N).map (fun z => (history p N z,(fun i => rowStageCost p N i z),rowTotalCost p N z)) := by
  congr 1
  funext z
  rw [rowHistory_value]
end QEC.Coding.BDL26IncomingRowsExecution
