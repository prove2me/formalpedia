-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_finite_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:05:27.657782+00:00
-- url     : https://prove2.me/submissions/724aef71-cda2-44df-90f4-ddafe59d273b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_finite_iff
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_finite_prefix
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_original_stream_prefix
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamTotalCost p N omega < ∞ ↔
      ∀ i : Fin N, BDL26CountableEmbeddingExperiment.streamHalts p i.val omega := by
  rw [streamTotalCost_finite_prefix,totalCost_finite_iff]
  exact forall_congr' (fun i => (BDL26CountableEmbeddingExperiment.original_stream_prefix p N i 0 omega).2.2.1.symm)
end QEC.Coding.BDL26PaidRowsComposition
