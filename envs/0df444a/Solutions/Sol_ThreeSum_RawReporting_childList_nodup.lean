-- Prove2me | solution 1 for ThreeSum.RawReporting.childList_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:18.502077+00:00
-- url     : https://prove2.me/submissions/566ac244-f755-45ba-bf6b-421d46e0d51e

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting

set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
namespace ThreeSum.RawReporting
theorem _root_.solution {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) :
    (childList Q h).Nodup :=
  (Finset.sort_nodup _ _).map (fun _ _ h => h)
end ThreeSum.RawReporting
