-- Prove2me | solution 1 for ThreeSum.ReportingHostPositiveBatch.through_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:54:06.882987+00:00
-- url     : https://prove2.me/submissions/813df7a3-3254-4ec0-b435-9064b070961a

import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
import Theorems.Thm_ThreeSum_ReportingHostPositiveBatch_parentAt_eq_get

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPositiveBatch
open Finset BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostPositive
set_option linter.unusedSectionVars false
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.ReportingHostPositiveBatch
theorem _root_.solution {h J k j : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J) (hj : j < pres.length) :
    through I w pres hk (j+1) = through I w pres hk j ++ positiveChildren I w (parentAt pres j) hk := by
  rw [through,← List.take_append_getElem hj,List.flatMap_append,List.flatMap_singleton,parentAt_eq_get pres hj]
  rfl
end ThreeSum.ReportingHostPositiveBatch
