-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixCell.small_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:29.74424+00:00
-- url     : https://prove2.me/submissions/800ca6b1-02c5-4c25-ad47-3c84b80c4502

import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixCell
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixCell
theorem _root_.solution {W V : ℕ} (hV : V ≤ W)
    (hw : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    (((V+1)*2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
  have hm := Nat.mul_le_mul (Nat.succ_le_succ hV)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.succ_le_succ hV))
  exact (by exact_mod_cast hm : (((V+1)*2^(V+1) : ℕ) : ℤ) ≤
    (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hw
end ThreeSum.LightReportingSuffixCell
