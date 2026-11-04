-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.space_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:15:54.467204+00:00
-- url     : https://prove2.me/submissions/f003c187-070d-4581-b17c-df5c21d3a984

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_WeightedCache3SUM_Alias_f0a4e431f2aa2c77
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution {n work : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.space work (Scales.microHalf (Scales.inputBits n)) ≤
      work+Scales.localSearch 2000 n :=
  (space_bound _ _).trans (Nat.add_le_add_left (envelope_le_search hh) work)
end ThreeSum.LocalParameterBounds
