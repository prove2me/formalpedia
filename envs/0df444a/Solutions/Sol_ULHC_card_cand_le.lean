-- Prove2me | solution 1 for ULHC.card_cand_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:04:48.549695+00:00
-- url     : https://prove2.me/submissions/9c9ffe16-7342-47ac-86de-896aaf91cc80

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_card_allStrips


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution (G : Finset Edge) :
    (cand V G).card ≤ 4 * V.card + V.card * (4 * V.card) := by
  unfold cand
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add (card_allStrips (V := V) (F := G)) ?_)
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (fun u _ => card_allStrips (V := V) (F := flip G u))).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
end ULHC
