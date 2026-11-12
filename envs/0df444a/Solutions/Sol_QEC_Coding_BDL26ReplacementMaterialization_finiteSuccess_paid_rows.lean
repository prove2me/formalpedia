-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.finiteSuccess_paid_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:22:30.760383+00:00
-- url     : https://prove2.me/submissions/f39e0871-8c81-497c-b531-99b6abd78467

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_stageFacts


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) (h : z ∈ finiteSuccess p N) (i : Fin N) :
    PhysicalSuccessorFacts p i.val (stageInput p N i z) (tableAt p N i z) ∧
      extendedTotalCost p N z < ∞ :=
  ⟨finiteSuccess_stageFacts p N h i,extendedTotalCost_finite_on_success p N z h⟩
end QEC.Coding.BDL26ReplacementMaterialization
