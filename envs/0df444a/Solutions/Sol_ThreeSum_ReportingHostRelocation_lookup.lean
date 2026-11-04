-- Prove2me | solution 1 for ThreeSum.ReportingHostRelocation.lookup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:57:20.584991+00:00
-- url     : https://prove2.me/submissions/add1907d-8280-4373-b826-c205dc9e9af6

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_P2M_Light_getElem__append_length_add_3291fe153891


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostRelocation
open Light
namespace ThreeSum.ReportingHostRelocation
theorem _root_.solution {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body) (prefixProgram : Program) :
    (program prefixProgram P)[prefixProgram.length+p]? = some (relocate prefixProgram.length body) := by
  apply getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl
end ThreeSum.ReportingHostRelocation
