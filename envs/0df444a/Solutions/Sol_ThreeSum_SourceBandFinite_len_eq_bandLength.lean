-- Prove2me | solution 1 for ThreeSum.SourceBandFinite.len_eq_bandLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:14:45.12496+00:00
-- url     : https://prove2.me/submissions/ced8365b-16b1-4939-854d-e7d4c2355d88

import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
import Definitions.Def_Submission_ThreeSum_SourceBandFinite

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandFinite
open GlobalEncoding OutputDecodeRecords
namespace ThreeSum.SourceBandFinite
theorem _root_.solution (n g i : ℕ) : SourceBandLayout.len n g i=BandRawA.bandLength n g i := rfl
end ThreeSum.SourceBandFinite
