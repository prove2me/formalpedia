-- Prove2me | solution 1 for QEC.Coding.BDL26IncomingRowsExecution.measurable_rowStepQuery_prefix_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:38:05.605306+00:00
-- url     : https://prove2.me/submissions/9b1f9c99-cb53-4288-b8a2-f21af7b6a4df

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowPrefixQuery_rep
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_rowScanQuery_prefix
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowStepQuery_cost_labels
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_JumpProtected_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


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
theorem _root_.solution (P : TannerSquarePresentation) {r : ℝ}
    (hr : 0 ≤ r) (lambda : ℝ) (K s : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let I := incomingRows P w.1
      let R := (rowPrefixQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 s).1
      (rowStepQuery P I r lambda K (rowUniverseQuery P I hr).1 w.2 R).2) := by
  have hs := measurable_rowScanQuery_prefix P hr lambda K s
  have hm : Measurable (fun e : Option (MasterEvent P) =>
      match e with | none => 0 | some e => countedMasterRefreshCost P e) := measurable_of_countable _
  convert hs.snd.add (hm.comp hs.fst) using 1
  funext w
  exact rowStepQuery_cost_labels P (incomingRows P w.1) r lambda K _ w.2 _
    (rowPrefixQuery_rep P (incomingRows P w.1) hr lambda K w.2 s).1
end QEC.Coding.BDL26IncomingRowsExecution
