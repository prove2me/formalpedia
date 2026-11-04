-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.word_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:55.826735+00:00
-- url     : https://prove2.me/submissions/7ccf7343-9f08-41a1-b361-bc704323d4bf

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.word (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n :=
  (word_bound _).trans (envelope_le_search hh)
end ThreeSum.LocalParameterBounds
