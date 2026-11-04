-- Prove2me | solution 1 for ThreeSum.ReportingHostRelocation.ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:03:52.154216+00:00
-- url     : https://prove2.me/submissions/2975a357-64f5-457d-a0d7-61d57930ef16

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_ThreeSum_ReportingHostRelocation_exec

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostRelocation
open Light
namespace ThreeSum.ReportingHostRelocation
theorem _root_.solution {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (prefixProgram : Program) :
    Ends lim (program prefixProgram P) d (relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,exec he prefixProgram,hc,hq⟩
end ThreeSum.ReportingHostRelocation
