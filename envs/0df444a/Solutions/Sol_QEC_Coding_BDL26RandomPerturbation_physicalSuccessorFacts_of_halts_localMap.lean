-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physicalSuccessorFacts_of_halts_localMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:02:54.49213+00:00
-- url     : https://prove2.me/submissions/dc6c228d-3e84-405e-b59f-665d84cfe154

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_physicalGeometry_of_localMap
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported


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
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (hh : Halts (eventSupport (state (perturbationOddScale p) n).presentation J (anchorRadius p.m))
      (eventBad (state (perturbationOddScale p) n).presentation J
        (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)
    (hg : IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
      (physicalSuccessorOutput p n J T) p.t) : PhysicalSuccessorFacts p n J T :=
  ⟨hh,hg,physicalGeometry_of_localMap _ _ _ hg,
    BDL26CSSDaviesLocality.frequency_supported _ _,
    BDL26CSSDaviesLocality.weightedJump_supported _ _⟩
end QEC.Coding.BDL26RandomPerturbation
