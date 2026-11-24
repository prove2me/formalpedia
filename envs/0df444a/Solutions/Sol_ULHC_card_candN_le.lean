-- Prove2me | solution 1 for ULHC.card_candN_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:07:32.415723+00:00
-- url     : https://prove2.me/submissions/6adef81e-0fea-4ee4-89c7-0cf1ed749293

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Counts
import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_card_cand_le
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt}
namespace ULHC
theorem _root_.solution (G : Finset Edge) : (candN V G).card ≤ Bd V := by
  unfold candN Bd
  refine Finset.card_biUnion_le.trans ?_
  have h3 : ∀ σ ∈ cand V G,
      (({1, 2, 3} : Finset ℕ).image fun p => Node.mk σ p).card ≤ 3 := fun σ _ =>
    Finset.card_image_le.trans (by simp)
  refine (Finset.sum_le_sum h3).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  have := card_cand_le (V := V) G
  omega
end ULHC
