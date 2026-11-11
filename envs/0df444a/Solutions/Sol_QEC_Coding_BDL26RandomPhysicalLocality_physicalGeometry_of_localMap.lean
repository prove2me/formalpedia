-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.physicalGeometry_of_localMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:02:44.427293+00:00
-- url     : https://prove2.me/submissions/ff58fb70-fc94-4922-8102-2686cfa4c9bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_qubit_density_le
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_check_radius
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_check_diameter
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_radius
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_region_diameter
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_check_card_le_seven
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_region_card_le_fifty
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_region_diameter


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
    (hJ : IsBoundedDensityLocalMap (state S n).presentation J t) : PhysicalGeometry S n J t := by
  refine ⟨?_, ?_, ?_⟩
  · exact qubit_density_le _ (state S n).admissible.toTannerSquareAdmissible J hJ
  · intro j
    exact ⟨check_radius S n J hJ j,
      fun r hr s hs => check_diameter S n J hJ j r s hr hs, check_card_le_seven S n j⟩
  · intro q
    exact ⟨region_radius S n J hJ q,
      fun r hr s hs => region_diameter S n J hJ q r s hr hs, region_card_le_fifty S n q⟩
end QEC.Coding.BDL26RandomPhysicalLocality
