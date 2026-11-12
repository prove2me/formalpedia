-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.uniform_outputAt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:29:47.914618+00:00
-- url     : https://prove2.me/submissions/f536f05b-cdb8-4d04-b457-2f7c736beb9e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_outputAt_top


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (S : OddScale) (j : Nat) :
    outputAt S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
      (Fin.last (2 * j + 1)) = BDL26UniformHistoryObstruction.topOutput S j :=
  outputAt_top S (2 * j + 1) _
end QEC.Coding.BDL26CanonicalHistoryMarks
