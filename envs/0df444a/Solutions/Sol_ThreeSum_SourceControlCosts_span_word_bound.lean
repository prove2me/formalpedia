-- Prove2me | solution 1 for ThreeSum.SourceControlCosts.span_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:51:41.528536+00:00
-- url     : https://prove2.me/submissions/b086f082-27ff-47aa-85db-2340acd5d3d2

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceControlCosts

set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceControlCosts
theorem _root_.solution {J W K S logP logE : ℕ} (hS : 0 < S) :
    SourceControlLayout.word J W K S logP logE ≤
      9*SourceControlLayout.span J W K S logP logE+30 := by
  have hstride : SourceControlLayout.stride W K ≤ S*SourceControlLayout.stride W K :=
    Nat.le_mul_of_pos_left _ hS
  have hstridePos : 0 < SourceControlLayout.stride W K := by unfold SourceControlLayout.stride; omega
  have hScount : S ≤ S*SourceControlLayout.stride W K := Nat.le_mul_of_pos_right _ hstridePos
  have hJ : J ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_succ _).trans (le_max_right _ _)
  have hP : logP ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_add_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hE : logE ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_add_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hquad : (W+1)^2 ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_add_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  unfold SourceControlLayout.word SourceControlLayout.span
  omega
end ThreeSum.SourceControlCosts
