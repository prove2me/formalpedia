-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.materializationCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:29:30.542505+00:00
-- url     : https://prove2.me/submissions/125036dd-86a5-4a09-a0e9-dd9afe938822

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_emittedRows_length
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_materializeRows_cost_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26ReplacementMaterialization
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : materializationCost p n w ≤
      65536*(Fintype.card (Vertex (StagePresentation p n))+1)*
        Fintype.card (Vertex (StagePresentation p (n+1))) := by
  have h := materializeRows_cost_le p n (emittedRows p n w.1 w.2)
  rw [emittedRows_length] at h
  exact h
end QEC.Coding.BDL26ReplacementMaterialization
