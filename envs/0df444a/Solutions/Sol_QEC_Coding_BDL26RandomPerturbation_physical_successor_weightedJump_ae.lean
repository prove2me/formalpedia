-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physical_successor_weightedJump_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:37:21.923172+00:00
-- url     : https://prove2.me/submissions/beed75d0-fd8c-4fd8-bc7c-5a02ba1703d4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_localMap_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_weightedJump_physical
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


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
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t)
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) (n+1) →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) (n+1) → ℝ)
    (q : Physical (perturbationOddScale p) (n+1)) (a : CSSDaviesLocality.Axis)
    (ω : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) (n+1)) :
    ∀ᵐ T ∂physicalTableLaw p n,
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).OperatorSupportedOnRegister
        (hamiltonianJump (hamiltonian (perturbationOddScale p) (n+1))
          (BDL26CSSDaviesLocality.hamiltonian_symmetric _ _)
          (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) (n+1) =>
            BDL26CSSDaviesLocality.coupling _ _ qa.1 qa.2) rate ((q,a),ω)) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q q)) ≤ 2) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        ∀ s ∈ region (perturbationOddScale p) (n+1) q,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 4) ∧
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).selected.card ≤ 50 := by
  filter_upwards [physical_successor_localMap_ae p n J hJ] with T hT
  exact weightedJump_physical _ _ _ hT rate q a ω
end QEC.Coding.BDL26RandomPerturbation
