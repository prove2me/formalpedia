-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.stageMaterializationCost_static
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:01:05.272005+00:00
-- url     : https://prove2.me/submissions/1a128374-0ebf-4131-943e-baef0ab4ce95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_materializationCost_static

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
    (i : Fin N) (z : Experiment p N) :
    stageMaterializationCost p N i z = materializationLabelCost p i.val :=
  materializationCost_static p i.val (stagePair p N i z)
end QEC.Coding.BDL26ReplacementMaterialization
