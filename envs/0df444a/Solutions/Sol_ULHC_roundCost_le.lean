-- Prove2me | solution 1 for ULHC.roundCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:38.66682+00:00
-- url     : https://prove2.me/submissions/c6581454-2ffa-4e86-9e04-0e31b27be15f

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
import Theorems.Thm_ULHC_findT3Cost_le
import Theorems.Thm_ULHC_findPathCost_le
import Theorems.Thm_ULHC_ACell_split
import Theorems.Thm_ULHC_findPath_some
import Theorems.Thm_ULHC_len_le_card


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hG : Deg2 V G) : roundCost V G ≤ 7000000 * (V.card + 1) ^ 8 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h1 := findT3Cost_le hG.1
  have h2 := findPathCost_le hG.1
  have h4 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 8 := Nat.pow_le_pow_right hN (by omega)
  have h5 : V.card + 1 ≤ (V.card + 1) ^ 8 := Nat.le_self_pow (by omega) _
  have ha : ∀ a L, findPath V G = some (a, L) → applySCost a ≤ 8 * V.card + 1 := by
    intro a L hp
    have hv := (findPath_some hG.1 hp).1.1.1
    have := len_le_card hv.2.2.1
    unfold applySCost flipCost; omega
  unfold roundCost
  split
  · unfold flipCost; omega
  · split
    · rename_i a L hp
      have := ha a L hp
      show findT3Cost V G + (findPathCost V G + applySCost a) ≤ _
      omega
    · show findT3Cost V G + (findPathCost V G + 0) ≤ _
      omega
end ULHC
