-- Prove2me | solution 1 for ThreeSum.ReportingHostPositiveBatch.parentAt_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:54:08.169726+00:00
-- url     : https://prove2.me/submissions/87ee7344-842c-4436-98dc-cf5ad291fb25

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
theorem _root_.solution {h J k i : ℕ} (q : GlobalOutput h J)
    (pres : List (List (Finset (Fin (512*h))))) (hp : ∀ pre ∈ pres, ValidPrefix q k pre)
    (hi : i < pres.length) : ValidPrefix q k (parentAt pres i) := by
  rw [parentAt_eq_get pres hi]
  exact hp _ (List.getElem_mem hi)
end ThreeSum.ReportingHostPositiveBatch
