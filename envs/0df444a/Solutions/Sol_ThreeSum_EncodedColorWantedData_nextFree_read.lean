-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedData.nextFree_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:33:03.131704+00:00
-- url     : https://prove2.me/submissions/fa4e7ce4-e509-4a3c-b73c-2ee44aabfd79

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedData
open Light WantedResidueKeys
namespace ThreeSum.EncodedColorWantedData
theorem _root_.solution {μ : ℕ → ℤ} {out M NL NR : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift) :
    μ (out+2)=(nextFree out M left right NL NR shift : ℤ) := H.2.2.1
end ThreeSum.EncodedColorWantedData
