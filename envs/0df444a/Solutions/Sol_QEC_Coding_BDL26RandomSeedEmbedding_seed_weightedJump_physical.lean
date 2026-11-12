-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_weightedJump_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:01:45.256495+00:00
-- url     : https://prove2.me/submissions/58696e02-1632-417a-b883-3f9e975d8bc1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_distance_zero
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_region_card
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomSeedEmbedding
theorem _root_.solution (S : OddScale)
    (rate : BDL26CSSDaviesLocality.CouplingIndex S 0 → BDL26CSSDaviesLocality.Frequency S 0 → ℝ)
    (q : Physical S 0) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S 0) :
    (BDL26CSSDaviesLocality.subsystem S 0 q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian S 0) (BDL26CSSDaviesLocality.hamiltonian_symmetric S 0)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex S 0 =>
          BDL26CSSDaviesLocality.coupling S 0 qa.1 qa.2) rate ((q,a),ω)) ∧
    (∀ r ∈ region S 0 q, dist (seedPoint S (.q r)) (seedPoint S (.q q)) = 0) ∧
    (∀ r ∈ region S 0 q, ∀ s ∈ region S 0 q,
      dist (seedPoint S (.q r)) (seedPoint S (.q s)) = 0) ∧
    (BDL26CSSDaviesLocality.subsystem S 0 q).selected.card ≤ 5 :=
  ⟨BDL26CSSDaviesLocality.weightedJump_supported S 0 rate q a ω,
    fun r _ => seed_physical_distance_zero S r q,
    fun r _ s _ => seed_physical_distance_zero S r s, seed_region_card S q⟩
end QEC.Coding.BDL26RandomSeedEmbedding
