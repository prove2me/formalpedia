-- Prove2me | solution 1 for ThreeSum.ReportingHostRelocation.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:56.714741+00:00
-- url     : https://prove2.me/submissions/3c347d60-aaec-414c-8bf2-0d5e1d945eaa

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_ThreeSum_ReportingHostRelocation_lookup
import Theorems.Thm_ThreeSum_ReportingHostRelocation_ends

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostRelocation
open Light
namespace ThreeSum.ReportingHostRelocation
theorem _root_.solution {lim : Limits} {P : Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : Meets lim P p d vals μ T R) (prefixProgram : Program) :
    Meets lim (program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨relocate prefixProgram.length body,lookup hbody prefixProgram,ends he prefixProgram⟩
end ThreeSum.ReportingHostRelocation
