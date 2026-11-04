-- Prove2me | solution 1 for ThreeSum.ColorParameters.fields_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:51.825487+00:00
-- url     : https://prove2.me/submissions/28cb21e0-9e6c-49f4-b565-4f8c6f6b0836

import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Mathlib.Data.List.FinRange
import Definitions.Def_Submission_ThreeSum_ColorParameters

set_option autoImplicit false
open ThreeSum ThreeSum.ColorParameters
namespace ThreeSum.ColorParameters
theorem _root_.solution {W t : ℕ} (ht : t < count W) : fields (parameter ht)=data W t := rfl
end ThreeSum.ColorParameters
