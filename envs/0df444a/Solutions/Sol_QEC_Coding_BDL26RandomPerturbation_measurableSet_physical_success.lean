-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurableSet_physical_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:03:36.231509+00:00
-- url     : https://prove2.me/submissions/e55913f9-0031-4ffd-9d9a-0ccecd11fe06

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_boundedDensityLocalMap
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_joint_halts


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet {z :
      (Vertex (state (perturbationOddScale p) n).presentation → Space) ×
        Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space) |
      Halts (eventSupport (state (perturbationOddScale p) n).presentation z.1 (anchorRadius p.m))
        (eventBad (state (perturbationOddScale p) n).presentation z.1
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) z.2 ∧
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
        (physicalSuccessorOutput p n z.1 z.2) p.t} :=
  (measurableSet_joint_halts _ _ _ _).inter
    ((measurableSet_boundedDensityLocalMap _ _).preimage
      (measurable_joint_physicalSuccessorOutput p n))
end QEC.Coding.BDL26RandomPerturbation
