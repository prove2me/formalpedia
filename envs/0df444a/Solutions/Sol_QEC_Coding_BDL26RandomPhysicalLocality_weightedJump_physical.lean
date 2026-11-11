-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.weightedJump_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:50:17.737393+00:00
-- url     : https://prove2.me/submissions/378a65fb-43e2-4a44-8760-97bd7cb2d129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_radius
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_diameter
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_region_card_le_fifty
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_region_diameter
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26RandomPhysicalLocality
theorem _root_.solution (S : OddScale) (n : Nat)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (rate : BDL26CSSDaviesLocality.CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S n) :
    (BDL26CSSDaviesLocality.subsystem S n q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian S n) (BDL26CSSDaviesLocality.hamiltonian_symmetric S n)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex S n =>
          BDL26CSSDaviesLocality.coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem S n q).selected.card ≤ 50 :=
  ⟨BDL26CSSDaviesLocality.weightedJump_supported S n rate q a ω, region_radius S n J hJ q,
    fun r hr s hs => region_diameter S n J hJ q r s hr hs, region_card_le_fifty S n q⟩
end QEC.Coding.BDL26RandomPhysicalLocality
