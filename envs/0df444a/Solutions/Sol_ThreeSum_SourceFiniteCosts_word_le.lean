-- Prove2me | solution 1 for ThreeSum.SourceFiniteCosts.word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:07:17.089138+00:00
-- url     : https://prove2.me/submissions/fb8dbf22-c5ac-4ca1-8ffc-79f8f0624b58

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Theorems.Thm_ThreeSum_SourceFiniteCosts_word_mono
import Theorems.Thm_ThreeSum_SourceBandBankLayout_word_mono


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceFiniteCosts
theorem _root_.solution {NL NR n p U D : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.word NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ word n p U D :=
  word_mono hNL hNR
end ThreeSum.SourceFiniteCosts
