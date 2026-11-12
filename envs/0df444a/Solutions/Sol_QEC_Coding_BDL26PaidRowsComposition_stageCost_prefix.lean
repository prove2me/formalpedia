-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.stageCost_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:40:16.774102+00:00
-- url     : https://prove2.me/submissions/45882f1b-179a-4271-b1db-c20d4e0afc4e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageCost_eq
import Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_rowStageCost_prefix
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_stageMaterializationCost_prefix


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26PaidRowsComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {M N : ℕ} (h : M ≤ N)
    (i : Fin M) (z : Experiment p N) :
    stageCost p M i (experimentPrefix p M N h z) = stageCost p N (i.castLE h) z := by
  rw [stageCost_eq,stageCost_eq,rowStageCost_prefix,stageMaterializationCost_prefix]
  rfl
end QEC.Coding.BDL26PaidRowsComposition
