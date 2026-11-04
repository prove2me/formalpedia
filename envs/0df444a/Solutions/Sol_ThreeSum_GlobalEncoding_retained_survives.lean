-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.retained_survives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:06.660555+00:00
-- url     : https://prove2.me/submissions/d165ac30-0688-462a-a6ee-dda838f33ae5

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
theorem _root_.solution {h : ℕ} (c : RetainedChoice h) :
    Survives h (occurrence c) (edge c) := c.property
end ThreeSum.GlobalEncoding
