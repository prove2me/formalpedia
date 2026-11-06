-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.hasNoIsolatedVertices_of_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:50:39.964893+00:00
-- url     : https://prove2.me/submissions/563c4918-fdab-4df7-a770-e5537eb8d135

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance

set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
open QEC.Coding.ClassicalWeightReduction
variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [DecidableEq Check] [DecidableEq Bit]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    (hBit : ∀ b : Bit, 0 < Fintype.card (BitNeighbor R b))
    (hCheck : ∀ c : Check, 0 < Fintype.card (CheckNeighbor R c)) :
    HasNoIsolatedVertices R where
  bit_nonempty b := Fintype.card_pos_iff.mp (hBit b)
  check_nonempty c := Fintype.card_pos_iff.mp (hCheck c)
end QEC.Coding.ClassicalWeightReduction
