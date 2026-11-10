-- Prove2me | solution 1 for QEC.Coding.BDL26RXLocalReplacement.rxCxCocycle_eq_boundaryRoot_zeroCopy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:02:18.20607+00:00
-- url     : https://prove2.me/submissions/90b4e9f5-a668-4ddc-b434-c92f8b85c8a7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_eq_on_subdivisionVertex
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxCocycle_copy_one_eq_zero_at_boundaryRoot
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u
namespace QEC.Coding.BDL26RXLocalReplacement
theorem _root_.solution
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderVertex P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary1 word = 0)
    (vertex : DoubleCylinderVertex P x S) :
    word vertex =
      word (0,
        (subdivisionOriginalBoundaryVertex P x S (A.xBoundaryRoot x)).1) := by
  rcases vertex with ⟨copy, vertex⟩
  fin_cases copy
  · exact rxCxCocycle_eq_on_subdivisionVertex
      P A x S 0 word hword vertex
  · exact (rxCxCocycle_eq_on_subdivisionVertex
      P A x S 1 word hword vertex).trans
        (rxCxCocycle_copy_one_eq_zero_at_boundaryRoot P A x S word hword)
end QEC.Coding.BDL26RXLocalReplacement
