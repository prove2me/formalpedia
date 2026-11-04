-- Prove2me | solution 1 for ThreeSum.EncodedColorLayout.prime_le_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:58:59.061314+00:00
-- url     : https://prove2.me/submissions/d61ce0a6-04ff-48cb-a0e9-670041f50cca

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_EncodedColorLayout

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorLayout
theorem _root_.solution (free n g M y : ℕ) : prime free n g+6 ≤ cover free n g M y := by
  unfold cover EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  omega
end ThreeSum.EncodedColorLayout
