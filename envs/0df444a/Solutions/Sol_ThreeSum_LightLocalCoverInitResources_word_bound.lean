-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:29.092699+00:00
-- url     : https://prove2.me/submissions/07191216-6536-4e16-81cb-35ea9edb1d68

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_parameters_envelope_le
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_four_envelope_le
import Theorems.Thm_ThreeSum_LightLocalCoverResources_word_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution (h : ℕ) : LightLocalCoverInit.word h ≤ envelope h := by
  have hp := (LocalParameterBounds.word_bound h).trans (parameters_envelope_le h)
  have hc := LightLocalCoverResources.word_bound h
  apply (show LightLocalCoverInit.word h ≤ 4*LightLocalCoverResources.envelope h from ?_).trans
    (four_envelope_le h)
  unfold LightLocalCoverInit.word
  omega
end ThreeSum.LightLocalCoverInitResources
