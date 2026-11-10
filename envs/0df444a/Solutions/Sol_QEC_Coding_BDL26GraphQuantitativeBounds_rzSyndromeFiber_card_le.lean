-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.rzSyndromeFiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T05:15:43.120264+00:00
-- url     : https://prove2.me/submissions/f24f4909-15c0-41c9-abc9-bcb13f526bb8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_doubleCylinderVertex_card_le
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_boundedValence_transpose
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
open BDL26ReplacementSupport
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) (S : OddScale) (z : P.Z) :
    Fintype.card {c : BDL26RZLocalReplacement.RZZ P S //
      rzSyndromeOwner P S c = z} ≤ localCoordinateBound S := by
  classical
  let f : ZDoubleCylinderVertex P z S →
      {c : BDL26RZLocalReplacement.RZZ P S // rzSyndromeOwner P S c = z} :=
    fun a => ⟨⟨z,a⟩,rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨⟨z',a⟩,hz⟩
    change z' = z at hz
    subst z'
    exact ⟨a,rfl⟩
  exact (Fintype.card_le_of_surjective f hf).trans
    (doubleCylinderVertex_card_le (transposePresentation P)
      (transposeTannerSquareAdmissible P A) (boundedValence_transpose P h) z S)
end QEC.Coding.BDL26GraphQuantitativeBounds
