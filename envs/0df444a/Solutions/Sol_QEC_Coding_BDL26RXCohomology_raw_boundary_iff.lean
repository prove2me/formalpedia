-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.raw_boundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:06:39.992592+00:00
-- url     : https://prove2.me/submissions/883dfe9f-b1cc-4e6a-a96a-265291b41034

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_map1_injective
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_potential_is_map0
import Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap_commutes_coboundary0
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (v : Word Field P.Q) :
    (∃ f, rxCoboundary0 P S f = rxMap1Coord P S v) ↔
      ∃ old, tannerCoboundary0 P old = v := by
  constructor
  · rintro ⟨f,hf⟩
    have hx : ∀ x e, rxCoboundary0 P S f (Sum.inl ⟨x,e⟩) = 0 := by
      intro x e
      rw [hf, rxMap1Coord_localEdge]
    obtain ⟨old,ho⟩ := potential_is_map0 P A S f hx
    refine ⟨old, map1_injective P S ?_⟩
    have hc := LinearMap.congr_fun (rxMap_commutes_coboundary0 P A S) old
    change rxCoboundary0 P S (rxMap0Coord P S old) =
      rxMap1Coord P S (tannerCoboundary0 P old) at hc
    rw [ho, hf] at hc
    exact hc.symm
  · rintro ⟨old,rfl⟩
    refine ⟨rxMap0Coord P S old, ?_⟩
    exact LinearMap.congr_fun (rxMap_commutes_coboundary0 P A S) old
end QEC.Coding.BDL26RXCohomology
