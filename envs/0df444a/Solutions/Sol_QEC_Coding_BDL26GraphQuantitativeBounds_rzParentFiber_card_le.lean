-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.rzParentFiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:49:38.501476+00:00
-- url     : https://prove2.me/submissions/4cc45348-0503-479e-bbd5-4ff8ef38c588

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (u : Vertex P) :
    Fintype.card {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) //
      rzParent P A S v = some u} ≤ Fintype.card (RZZeroCell P S u) := by
  classical
  let f : RZZeroCell P S u →
      {v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) //
        rzParent P A S v = some u} :=
    fun a => ⟨rzZeroInclude P A S u a,(rzParent_iff P A S u _).mpr ⟨a,rfl⟩⟩
  apply Fintype.card_le_of_surjective f
  rintro ⟨v,hv⟩
  obtain ⟨a,ha⟩ := (rzParent_iff P A S u v).mp hv
  exact ⟨a,Subtype.ext ha⟩
end QEC.Coding.BDL26GraphQuantitativeBounds
