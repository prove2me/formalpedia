-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physical_successor_random_input_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:28:44.163125+00:00
-- url     : https://prove2.me/submissions/9e7c93d8-1bac-4afb-864d-3bbfabb8b567

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorFacts_of_halts_localMap
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_physical_success
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_ae


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
    ∀ᵐ z ∂μ.prod (physicalTableLaw p n), PhysicalSuccessorFacts p n z.1 z.2 := by
  have hs := (Measure.ae_prod_iff_ae_ae (measurableSet_physical_success p n)).mpr (by
    filter_upwards [hμ] with J hJ
    filter_upwards [physical_successor_ae p n J hJ] with T hT
    exact ⟨hT.1,hT.2.1⟩)
  filter_upwards [hs] with z hz
  exact physicalSuccessorFacts_of_halts_localMap p n z.1 z.2 hz.1 hz.2
end QEC.Coding.BDL26RandomPerturbation
