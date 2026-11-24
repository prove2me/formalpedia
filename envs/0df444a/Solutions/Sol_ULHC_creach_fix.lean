-- Prove2me | solution 1 for ULHC.creach_fix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:53.149278+00:00
-- url     : https://prove2.me/submissions/cd3b493a-711b-4adb-8d91-da93f5dafc75

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_creach_sub_succ
import Theorems.Thm_ULHC_creach_sub
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
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
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution (hFV : Inside V F) {x : Pt} (hx : x ∈ V) :
    ∃ k ≤ V.card, creach F x (k + 1) = creach F x k := by
  by_contra hn
  push Not at hn
  have hgrow : ∀ n, n ≤ V.card + 1 → n + 1 ≤ (creach F x n).card := by
    intro n
    induction n with
    | zero => intro _; simp [creach]
    | succ n ih =>
      intro hn1
      have hss : creach F x n ⊂ creach F x (n + 1) :=
        ssubset_of_subset_of_ne creach_sub_succ (hn n (by omega)).symm
      have := card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hgrow (V.card + 1) le_rfl
  have h2 := card_le_card (creach_sub hFV hx (V.card + 1))
  omega
end ULHC
