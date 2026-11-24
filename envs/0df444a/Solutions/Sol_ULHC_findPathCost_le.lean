-- Prove2me | solution 1 for ULHC.findPathCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:13.452426+00:00
-- url     : https://prove2.me/submissions/0649bd9c-2d29-4fcd-a853-cdb9734ed62d

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
import Theorems.Thm_ULHC_decodeCost_le
import Theorems.Thm_ULHC_poly8
import Theorems.Thm_ULHC_MP_minPathCost_le
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_candNCost_le
import Theorems.Thm_ULHC_card_candN_le
import Theorems.Thm_ULHC_gedgeCost_le
import Theorems.Thm_ULHC_gsrcCost_le


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) : findPathCost V G ≤ 6000000 * (V.card + 1) ^ 8 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have hn : (candN V G).card ≤ 24 * (V.card + 1) ^ 2 := by
    have := card_candN_le (V := V) G; unfold Bd at this; nlinarith
  have hmp := MP.minPathCost_le (candN V G) gmid gtgt (gedge V G) gw (gedgeCost V G)
    (gsrcCost V G) (E := 300 * (V.card + 1) ^ 2) (S := 160 * (V.card + 1) ^ 2)
    (fun x hx y hy => gedgeCost_le hGV hx hy) (fun x _ => gsrcCost_le hGV x)
  have hp := poly8 (V.card + 1) _ hN hn
  have h1 := candNCost_le (V := V) G
  have h2 := decodeCost_le hGV
  have h3 : Dm V ≤ 24 * (V.card + 1) ^ 3 := by unfold Dm Bd; nlinarith
  have h4 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 8 := Nat.pow_le_pow_right hN (by omega)
  unfold findPathCost
  omega
end ULHC
