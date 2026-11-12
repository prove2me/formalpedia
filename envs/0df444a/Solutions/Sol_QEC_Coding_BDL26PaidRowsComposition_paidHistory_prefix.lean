-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.paidHistory_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:43:05.699732+00:00
-- url     : https://prove2.me/submissions/62671434-5267-4d40-ad5b-de8adc2c3de7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_paidHistory_original
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_prefix


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
    (z : Experiment p N) (i : Fin (M+1)) :
    paidHistory p M (experimentPrefix p M N h z) i =
      paidHistory p N z (i.castLE (by omega)) := by
  rw [paidHistory_original,paidHistory_original]
  exact history_prefix p h z i
end QEC.Coding.BDL26PaidRowsComposition
