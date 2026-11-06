-- Prove2me | solution 1 for QEC.Locality.bkTwoThirdsDepth_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:28:05.371227+00:00
-- url     : https://prove2.me/submissions/e12bf973-dbc9-4df5-b528-fad4ff8194b7

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkTwoThirdsDepth_eq_zero_of_terminal
import Theorems.Thm_QEC_Locality_bkTwoThirdsDepth_eq_succ
import Theorems.Thm_QEC_Locality_bkTwoThirdsChildScale_mono


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkTwoThirdsDepth d small ≤ bkTwoThirdsDepth d large := by
  induction large using Nat.strong_induction_on generalizing small with
  | h large ih =>
      by_cases hlargeTerminal : bkScaleTerminal d large
      · have hsmallTerminal : bkScaleTerminal d small := by
          rcases hlargeTerminal with hlargeZero | hlargeSmall
          · left
            omega
          · right
            omega
        rw [bkTwoThirdsDepth_eq_zero_of_terminal d small hsmallTerminal]
        rw [bkTwoThirdsDepth_eq_zero_of_terminal d large hlargeTerminal]
      · by_cases hsmallTerminal : bkScaleTerminal d small
        · rw [bkTwoThirdsDepth_eq_zero_of_terminal d small hsmallTerminal]
          exact Nat.zero_le _
        · rw [bkTwoThirdsDepth_eq_succ d small hsmallTerminal]
          rw [bkTwoThirdsDepth_eq_succ d large hlargeTerminal]
          apply Nat.add_le_add_left
          have hlargePositive : 0 < large := by
            by_contra hpositive
            apply hlargeTerminal
            exact Or.inl (Nat.eq_zero_of_not_pos hpositive)
          exact ih (bkTwoThirdsChildScale large)
            (bkTwoThirdsChildScale_lt large hlargePositive)
            (bkTwoThirdsChildScale_mono hscale)
end QEC.Locality
