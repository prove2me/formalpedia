-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixCell.small_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:32.264055+00:00
-- url     : https://prove2.me/submissions/ed75c7e7-b010-4f35-8b6d-249de7d20d80

import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixCell
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixCell
theorem _root_.solution {W V work : ℕ} (hV : V ≤ W)
    (hs : work+1+tableSize W+(W+1) ≤ lim.space) :
    work+tableSize V+(V+1) ≤ lim.space := by
  have hp := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
  change (V+1)^2 ≤ (W+1)^2 at hp
  unfold tableSize at *
  omega
end ThreeSum.LightReportingSuffixCell
