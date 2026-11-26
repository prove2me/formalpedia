-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_4_4_ii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:41.799537+00:00
-- url     : https://prove2.me/submissions/b1281bdb-2aa3-48b5-bc5b-f103a541cdd5

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app_one
import Theorems.Thm_Scott1976_DataTypesAsLattices_seq2_app_zero


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) :
    funOf (pairSeq x y) (ofNat 0) = x ∧
      funOf (pairSeq x y) (ofNat 1) = y :=
  ⟨seq2_app_zero x y, seq2_app_one x y⟩
end Scott1976.DataTypesAsLattices
