-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalConnectingWeight.fiber_neighbor_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:45:13.257288+00:00
-- url     : https://prove2.me/submissions/743bf700-db26-4dc4-af1d-59a56df925a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical
namespace QEC.Coding.BDL26XLocalConnectingWeight
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) :
    Function.Injective (fun d : Fiber P A x S e => d.val.1) := by
  rintro ⟨⟨qa, ea⟩, ha⟩ ⟨⟨qb, eb⟩, hb⟩ hq
  change qa = qb at hq
  subst qb
  have hedges : ea = eb :=
    qToXDoubleCylinderEdge_injective P A qa.val x qa.property S (ha.trans hb.symm)
  subst eb
  rfl
end QEC.Coding.BDL26XLocalConnectingWeight
