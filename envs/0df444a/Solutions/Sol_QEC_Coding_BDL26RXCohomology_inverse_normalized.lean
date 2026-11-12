-- Prove2me | solution 1 for QEC.Coding.BDL26RXCohomology.inverse_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:48:54.64485+00:00
-- url     : https://prove2.me/submissions/125a7531-aed5-464a-a0be-9b306cd0df4d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_inverse_gauge_class
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_differential1_eq
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_normalized_cocycle
import Theorems.Thm_QEC_Coding_BDL26RXCohomology_normalized_word
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXCohomology
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S))
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w.1 = 0) :
    ∃ v : Cocycle P, v.1 = coarseWord P S w.1 ∧
      (equiv P A R S).symm (classOf (rxReplacementPresentation P S) w) = classOf P v := by
  have hw : rxCoboundary1 P S w.1 = 0 := by
    rw [← differential1_eq P A R S]
    exact (BDL26RZCohomology.mem_cocycle_iff _ _).mp w.2
  let v : Cocycle P := ⟨coarseWord P S w.1,
    (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
      (normalized_cocycle P A.toTannerSquareAdmissible S w.1 hw hx)⟩
  refine ⟨v,rfl,inverse_gauge_class P A R S w v 0 ?_⟩
  rw [map_zero, sub_zero]
  exact normalized_word P A.toTannerSquareAdmissible S w.1 hw hx
end QEC.Coding.BDL26RXCohomology
