-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.frequency_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:50:14.216514+00:00
-- url     : https://prove2.me/submissions/4749aaff-2ba0-46e1-ad46-f28041549db0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_radius
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_diameter
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_region_card_le_fifty
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_region_diameter
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
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (BDL26CSSDaviesLocality.subsystem S n q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian S n) (BDL26CSSDaviesLocality.hamiltonian_symmetric S n)
        (BDL26CSSDaviesLocality.coupling S n q a) ω) ∧
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem S n q).selected.card ≤ 50 :=
  ⟨BDL26CSSDaviesLocality.frequency_supported S n q a ω, region_radius S n J hJ q,
    fun r hr s hs => region_diameter S n J hJ q r s hr hs, region_card_le_fifty S n q⟩
end QEC.Coding.BDL26RandomPhysicalLocality
