-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_perturbationEmbeddingOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:26:41.62791+00:00
-- url     : https://prove2.me/submissions/52348fea-5aa2-4ef6-9f18-dda97b027274

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_geometricOutput
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Measurable (perturbationEmbeddingOutput P J p) := by
  apply measurable_pi_lambda
  intro v
  exact measurable_const.add ((measurable_pi_apply v).comp (measurable_geometricOutput P J p))
end QEC.Coding.BDL26RandomPerturbation
