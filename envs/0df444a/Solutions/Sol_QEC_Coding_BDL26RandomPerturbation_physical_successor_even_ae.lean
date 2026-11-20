-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physical_successor_even_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:34:37.624624+00:00
-- url     : https://prove2.me/submissions/850fa3ec-a96a-4cb0-9dbf-5b8ad8d8e343

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_physicalGeometry_cast


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
theorem _root_.solution (p : GeometricParameters L) (k : Nat) (hk : 1 ≤ k)
    (J : Vertex (state (perturbationOddScale p) (2*k-1)).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) (2*k-1)).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p (2*k-1),
      PhysicalSuccessorFacts p (2*k-1) J T ∧
      PhysicalGeometry (perturbationOddScale p) (2*k)
        (fun v => physicalSuccessorOutput p (2*k-1) J T
          (cast (congrArg (fun m => Vertex (state (perturbationOddScale p) m).presentation)
            (show 2*k = (2*k-1)+1 by omega)) v)) p.t := by
  have he : (2*k-1)+1 = 2*k := by omega
  filter_upwards [physical_successor_ae p (2*k-1) J hJ] with T hT
  exact ⟨hT, physicalGeometry_cast _ _ _ he _ _ hT.2.2.1⟩
end QEC.Coding.BDL26RandomPerturbation
