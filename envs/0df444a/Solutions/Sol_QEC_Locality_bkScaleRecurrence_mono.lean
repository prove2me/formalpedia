-- Prove2me | solution 1 for QEC.Locality.bkScaleRecurrence_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:12.420067+00:00
-- url     : https://prove2.me/submissions/2f08c232-6db1-469b-b089-8b8b5ffdfef8

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Theorems.Thm_QEC_Locality_bkTwoThirdsChildScale_mono
import Theorems.Thm_QEC_Locality_bkScaleRecurrence_eq_zero_of_terminal
import Theorems.Thm_QEC_Locality_bkScaleRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_mono


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d : Nat) {small large : Nat} (hscale : small ≤ large) :
    bkScaleRecurrence G d small ≤ bkScaleRecurrence G d large := by
  induction large using Nat.strong_induction_on generalizing small with
  | h large ih =>
      by_cases hlargeTerminal : bkScaleTerminal d large
      · have hsmallTerminal : bkScaleTerminal d small := by
          rcases hlargeTerminal with hlargeZero | hlargeSmall
          · left
            omega
          · right
            omega
        rw [bkScaleRecurrence_eq_zero_of_terminal G d small hsmallTerminal]
        rw [bkScaleRecurrence_eq_zero_of_terminal G d large hlargeTerminal]
      · by_cases hsmallTerminal : bkScaleTerminal d small
        · rw [bkScaleRecurrence_eq_zero_of_terminal G d small hsmallTerminal]
          exact Nat.zero_le _
        · rw [bkScaleRecurrence_eq_profile_add G d small hsmallTerminal]
          rw [bkScaleRecurrence_eq_profile_add G d large hlargeTerminal]
          have hchildScale : bkTwoThirdsChildScale small ≤
              bkTwoThirdsChildScale large := bkTwoThirdsChildScale_mono hscale
          have hlargePositive : 0 < large := by
            by_contra h
            apply hlargeTerminal
            exact Or.inl (Nat.eq_zero_of_not_pos h)
          have hchildLt : bkTwoThirdsChildScale large < large :=
            bkTwoThirdsChildScale_lt large hlargePositive
          have hrecurrence := ih (bkTwoThirdsChildScale large) hchildLt hchildScale
          have hprofile := twoThirdsSeparationProfile_mono G hscale
          omega
end QEC.Locality
