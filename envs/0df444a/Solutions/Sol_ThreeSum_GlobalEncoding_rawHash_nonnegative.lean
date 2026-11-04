-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.rawHash_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:08.197197+00:00
-- url     : https://prove2.me/submissions/054eb850-981c-495f-8c1d-7cd86a003857

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    0 ≤ rawHash w s := Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
end ThreeSum.GlobalEncoding
