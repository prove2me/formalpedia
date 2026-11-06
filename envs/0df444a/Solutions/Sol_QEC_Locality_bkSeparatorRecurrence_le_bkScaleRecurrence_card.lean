-- Prove2me | solution 1 for QEC.Locality.bkSeparatorRecurrence_le_bkScaleRecurrence_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:23:45.497099+00:00
-- url     : https://prove2.me/submissions/753055b0-fff4-4115-9bcc-c2a0330d6658

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_eq_zero_of_terminal
import Theorems.Thm_QEC_Locality_bkSeparatorRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_bkScaleRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_bkScaleRecurrence_mono
import Theorems.Thm_QEC_Locality_card_le_bkTwoThirdsChildScale

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d : Nat) (vertices : Finset ι) :
    bkSeparatorRecurrence G d vertices ≤ bkScaleRecurrence G d vertices.card := by
  induction vertices using (measure Finset.card).wf.induction with
  | h vertices ih =>
      by_cases hterminal : bkSeparatorTerminal d vertices
      · rw [bkSeparatorRecurrence_eq_zero_of_terminal G d vertices hterminal]
        exact Nat.zero_le _
      · have hnonempty : vertices.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          exact hterminal (Or.inl hempty)
        let left := measuredTwoThirdsLeft G vertices
        let right := measuredTwoThirdsRight G vertices
        have hleftLt : left.card < vertices.card :=
          measuredTwoThirdsLeft_card_lt G vertices hnonempty
        have hrightLt : right.card < vertices.card :=
          measuredTwoThirdsRight_card_lt G vertices hnonempty
        have hleftRecurrence := ih left hleftLt
        have hrightRecurrence := ih right hrightLt
        have hsplit := measuredTwoThirdsSplit_spec G vertices
        have hleftScale : left.card ≤ bkTwoThirdsChildScale vertices.card :=
          card_le_bkTwoThirdsChildScale hsplit.2.2.2.1
        have hrightScale : right.card ≤ bkTwoThirdsChildScale vertices.card :=
          card_le_bkTwoThirdsChildScale hsplit.2.2.2.2.1
        have hleftMonotone := bkScaleRecurrence_mono G d hleftScale
        have hrightMonotone := bkScaleRecurrence_mono G d hrightScale
        have hleftBound : bkSeparatorRecurrence G d
              (measuredTwoThirdsLeft G vertices) ≤
            bkScaleRecurrence G d (bkTwoThirdsChildScale vertices.card) :=
          hleftRecurrence.trans hleftMonotone
        have hrightBound : bkSeparatorRecurrence G d
              (measuredTwoThirdsRight G vertices) ≤
            bkScaleRecurrence G d (bkTwoThirdsChildScale vertices.card) :=
          hrightRecurrence.trans hrightMonotone
        have hscaleNonterminal : ¬bkScaleTerminal d vertices.card := by
          intro hscale
          rcases hscale with hcardZero | hcardSmall
          · apply hterminal
            left
            exact Finset.card_eq_zero.mp hcardZero
          · exact hterminal (Or.inr hcardSmall)
        rw [bkSeparatorRecurrence_eq_profile_add G d vertices hterminal]
        rw [bkScaleRecurrence_eq_profile_add G d vertices.card hscaleNonterminal]
        omega
end QEC.Locality
