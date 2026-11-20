-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.exists_physical_successor_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:34:27.921373+00:00
-- url     : https://prove2.me/submissions/2f91875d-a67a-451e-9164-2b4a34b01e14

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


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
theorem _root_.solution (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower, ∀ (n : Nat)
      (J : Vertex (state (perturbationOddScale p) n).presentation → Space),
      IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t →
        ∀ᵐ T ∂physicalTableLaw p n, PhysicalSuccessorFacts p n J T := by
  obtain ⟨p⟩ := geometricParameters_nonempty densityLower
  exact ⟨p, physical_successor_ae p⟩
end QEC.Coding.BDL26RandomPerturbation
