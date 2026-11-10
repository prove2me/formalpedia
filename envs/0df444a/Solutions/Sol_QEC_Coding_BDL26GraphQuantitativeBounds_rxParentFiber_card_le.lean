-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.rxParentFiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:49:30.002598+00:00
-- url     : https://prove2.me/submissions/86bcb260-29fc-4947-a8a1-47fd0dad78df

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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (u : Vertex P) :
    Fintype.card {v : Vertex (rxReplacementPresentation P S) //
      rxParent P S v = some u} ≤ Fintype.card (RXZeroCell P S u) := by
  classical
  let f : RXZeroCell P S u → {v : Vertex (rxReplacementPresentation P S) //
      rxParent P S v = some u} :=
    fun a => ⟨rxZeroInclude P S u a,(rxParent_iff P S u _).mpr ⟨a,rfl⟩⟩
  apply Fintype.card_le_of_surjective f
  rintro ⟨v,hv⟩
  obtain ⟨a,ha⟩ := (rxParent_iff P S u v).mp hv
  exact ⟨a,Subtype.ext ha⟩
end QEC.Coding.BDL26GraphQuantitativeBounds
