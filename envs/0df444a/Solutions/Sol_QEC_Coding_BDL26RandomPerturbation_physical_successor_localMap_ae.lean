-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physical_successor_localMap_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:28:40.911198+00:00
-- url     : https://prove2.me/submissions/6c8d4e0f-def2-4cbf-8d61-5f1860bf5855

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_ae

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling MeasureTheory
variable {L : ℝ}
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
        (physicalSuccessorOutput p n J T) p.t := by
  filter_upwards [physical_successor_ae p n J hJ] with T hT
  exact hT.2.1
end QEC.Coding.BDL26RandomPerturbation
