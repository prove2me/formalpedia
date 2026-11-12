-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.common_row_execution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:31:33.116634+00:00
-- url     : https://prove2.me/submissions/09e06e7f-fdcd-432c-b958-74108c3eb2ae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowTotalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_geometry


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, rowTotalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega)<∞) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t :=
  ⟨fun N => rowTotalCost_finite_on_success p N _ (h N),
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_geometry p h⟩
end QEC.Coding.BDL26IncomingRowsExecution
