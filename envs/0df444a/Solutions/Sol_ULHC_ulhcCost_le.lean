-- Prove2me | solution 1 for ULHC.ulhcCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:06.293992+00:00
-- url     : https://prove2.me/submissions/b8134b53-a604-460e-843c-860b7e0bcc30

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
import Theorems.Thm_ULHC_runCost_le
import Theorems.Thm_ULHC_ACell_split
import Theorems.Thm_ULHC_twoFactorCost_le
import Theorems.Thm_ULHC_twoFactor_some


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (V : Finset Pt) : ulhcCost V ≤ 500000000 * (V.card + 1) ^ 12 := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h0 := twoFactorCost_le V
  have h3 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 12 := Nat.pow_le_pow_right hN (by omega)
  have hf : fuel V + 1 ≤ 55 * (V.card + 1) ^ 4 := by
    unfold fuel Dm Bd
    have a1 : 1 ≤ (V.card + 1) ^ 4 := Nat.one_le_pow _ _ hN
    nlinarith
  have h12 : (V.card + 1) ^ 4 * (V.card + 1) ^ 8 = (V.card + 1) ^ 12 := by rw [← pow_add]
  unfold ulhcCost
  split
  · rename_i F hF
    have := runCost_le (fuel V) F (twoFactor_some hF)
    have : V.card + 10 ≤ 11 * (V.card + 1) ^ 12 := by
      have := Nat.le_self_pow (n := 12) (by omega) (V.card + 1); omega
    nlinarith
  · have : V.card + 10 ≤ 11 * (V.card + 1) ^ 12 := by
      have := Nat.le_self_pow (n := 12) (by omega) (V.card + 1); omega
    omega
end ULHC
