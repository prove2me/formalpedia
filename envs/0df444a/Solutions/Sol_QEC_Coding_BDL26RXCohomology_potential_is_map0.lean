-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.potential_is_map0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:54:56.794453+00:00
-- url     : https://prove2.me/submissions/fbdc0b05-350c-4209-b7f5-0b060ec879bc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_raw_delta0_x
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_boundaryRoot_zeroCopy
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
    (S : OddScale) (f : Word Field (RX0 P S))
    (hf : ∀ x e, rxCoboundary0 P S f (Sum.inl ⟨x,e⟩) = 0) :
    ∃ old : Word Field P.X, rxMap0Coord P S old = f := by
  let old : Word Field P.X := fun x =>
    f ⟨x, (0, (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1)⟩
  refine ⟨old, ?_⟩
  funext p
  rcases p with ⟨x,v⟩
  symm
  apply rxCxCocycle_eq_boundaryRoot_zeroCopy P A x S (fun v => f ⟨x,v⟩)
  change wordLinearMapTranspose (doubleCylinderBoundary1 P x S) (fun v => f ⟨x,v⟩) = 0
  funext e
  rw [← raw_delta0_x P S f x e, hf]
  rfl
end QEC.Coding.BDL26RXCohomology
