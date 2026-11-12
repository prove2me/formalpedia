-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.common_paid_materialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:23:20.357524+00:00
-- url     : https://prove2.me/submissions/39c8c4f4-f2ea-4223-8d56-c9c60aedcf0f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_geometry


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, extendedTotalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega) < ∞) ∧
    ∀ n, PhysicalGeometry (perturbationOddScale p) n
      (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t :=
  ⟨fun N => extendedTotalCost_finite_on_success p N _ (h N),
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_geometry p h⟩
end QEC.Coding.BDL26ReplacementMaterialization
