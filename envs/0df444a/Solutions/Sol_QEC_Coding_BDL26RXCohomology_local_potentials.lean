-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.local_potentials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:54:24.414221+00:00
-- url     : https://prove2.me/submissions/fc7115d0-aeaf-4c85-951f-4ee711cd188d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_exact
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCx_global_restriction


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word Field (RX1 P S)) (hw : rxCoboundary1 P S w = 0) :
    ∃ f : ∀ x : P.X, Word Field (DoubleCylinderVertex P x S),
      ∀ x, wordLinearMapTranspose (localCx P S x).boundary1 (f x) =
        restrictWordLinear ((localX P S).correctionRegion x) w := by
  have hx : ∀ x, ∃ f : Word Field (DoubleCylinderVertex P x S),
      wordLinearMapTranspose (localCx P S x).boundary1 f =
        restrictWordLinear ((localX P S).correctionRegion x) w := by
    intro x
    apply LinearMap.mem_range.mp
    rw [← localCx_exact P A.toTannerSquareAdmissibleV3 R S x]
    apply LinearMap.mem_ker.mpr
    rw [← localCx_global_restriction, hw, map_zero]
  exact ⟨fun x => Classical.choose (hx x), fun x => Classical.choose_spec (hx x)⟩
end QEC.Coding.BDL26RXCohomology
