-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:17.963896+00:00
-- url     : https://prove2.me/submissions/e70ba5c4-6af6-4ee7-9340-f40331eda649

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}
namespace ThreeSum.LightKaratsuba
theorem _root_.solution : Procs program 0 1 2 3 := ⟨rfl, rfl, rfl, rfl⟩
end ThreeSum.LightKaratsuba
