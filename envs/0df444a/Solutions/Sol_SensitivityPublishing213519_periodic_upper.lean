-- Prove2me | solution 1 for SensitivityPublishing213519.periodic_upper
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T21:10:23.629683+00:00
-- url     : https://prove2.me/submissions/f650389d-256b-4674-a7ae-9ccbcd034c84

import Definitions.Def_BS2_b3ba934b_Endpoint16Complete
import Definitions.Def_BS2_b3ba934b_Endpoint16Assembly
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawNumerical0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawNumerical1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawNumerical2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawNumerical3
import Theorems.Thm_BS2_b3ba934b_Cert_RecordsComplete
set_option autoImplicit false

theorem solution : ∀ m : ℕ, ThreeBoundFullProfile.Upper (Sensitivity10007Endpoint16.family (4*m))
  (ThreeBoundFullProfile.scale (31192129^m) ThreeBoundMinmaxNumeric.Endpoint16.profile0) := by
  have hraw : ThreeBoundMinmaxNumeric.Endpoint16.RawNumericalBounds := by
    intro p
    fin_cases p
    · exact BS2_b3ba934b_Cert_16_RawNumerical0
    · exact BS2_b3ba934b_Cert_16_RawNumerical1
    · exact BS2_b3ba934b_Cert_16_RawNumerical2
    · exact BS2_b3ba934b_Cert_16_RawNumerical3
  exact ThreeBoundMinmaxNumeric.Endpoint16.periodic_upper
    (ThreeBoundEndpoint16Complete.raw_preserves_of_records BS2_b3ba934b_Cert_RecordsComplete) hraw
