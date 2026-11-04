-- Prove2me | solution 1 for ThreeSum.BlockCoefficientRows.occurrenceIndices_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:36:58.515708+00:00
-- url     : https://prove2.me/submissions/b461822d-b13c-4d0a-ad3e-c88ec7001000

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
attribute [local simp] ThreeSum.OneHotMask.extend_fin



set_option autoImplicit false
open ThreeSum ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds
namespace ThreeSum.BlockCoefficientRows
theorem _root_.solution {h J : ℕ} (o : Occurrences h J) (i : Fin J) :
    occurrenceIndices o i.val = (o i).val := by
  exact OneHotMask.extend_fin _ i
end ThreeSum.BlockCoefficientRows
