-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalGlobalPrelude.dimensionsLibrary_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:56:37.097975+00:00
-- url     : https://prove2.me/submissions/fbc1c840-d0c8-470c-b945-3faef84ff35e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalGlobalPrelude
open Light
namespace ThreeSum.LightWeightedGlobalGlobalPrelude
theorem _root_.solution (M b p K : ℕ) :
    (dimensionsLibrary M b p K).length=9 := rfl
end ThreeSum.LightWeightedGlobalGlobalPrelude
