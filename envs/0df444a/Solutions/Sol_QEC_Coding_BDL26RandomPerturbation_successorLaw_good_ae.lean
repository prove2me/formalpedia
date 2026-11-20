-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.successorLaw_good_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:50:55.286648+00:00
-- url     : https://prove2.me/submissions/4114ed3d-a83e-43a1-9fe9-67c6acf2c666

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorOutput_law
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_random_input_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_boundedDensityLocalMap


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ J ∂μ, IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ J' ∂(successorKernel p n) ∘ₘ μ,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation J' p.t := by
  rw [← physicalSuccessorOutput_law p n μ]
  apply (ae_map_iff (measurable_joint_physicalSuccessorOutput p n).aemeasurable
    (measurableSet_boundedDensityLocalMap _ _)).mpr
  filter_upwards [physical_successor_random_input_ae p n μ hμ] with z hz
  exact hz.2.1
end QEC.Coding.BDL26RandomPerturbation
