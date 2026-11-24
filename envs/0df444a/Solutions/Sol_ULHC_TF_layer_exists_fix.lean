-- Prove2me | solution 1 for ULHC.TF.layer_exists_fix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:34.323556+00:00
-- url     : https://prove2.me/submissions/7d4b924e-cb36-4111-8243-095e3794b972

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layer_sub_succ
import Theorems.Thm_ULHC_TF_layer_sub
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm


set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) :
    ∃ k ≤ V.card, layer V F (k + 1) = layer V F k := by
  by_contra hn
  push Not at hn
  have hgrow : ∀ n, n ≤ V.card + 1 → n ≤ (layer V F n).card := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn1
      have hss : layer V F n ⊂ layer V F (n + 1) :=
        ssubset_of_subset_of_ne layer_sub_succ (hn n (by omega)).symm
      have := card_lt_card hss
      have := ih (by omega)
      omega
  have h1 := hgrow (V.card + 1) le_rfl
  have h2 := card_le_card (layer_sub (V := V) (F := F) (V.card + 1))
  omega
end ULHC.TF
