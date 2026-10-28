-- Prove2me | solution 1 for SensitivityPublishing213303.periodic_upper
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:06:27.274783+00:00
-- url     : https://prove2.me/submissions/1e51f5a3-3870-4f37-9f76-8b0fcdcf5040

import Definitions.Def_BS2_b3ba934b_Endpoint40Campaign
import Definitions.Def_BS2_b3ba934b_Endpoint40Assembly
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawNumerical0
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawNumerical1
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawNumerical2
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawNumerical3
import Theorems.Thm_BS2_b3ba934b_Cert_RecordsComplete
set_option autoImplicit false

theorem solution : ∀ m : ℕ, ThreeBoundFullProfile.Upper (Sensitivity10007Endpoint40.family (4*m))
  (ThreeBoundFullProfile.scale (31739938^m) ThreeBoundNumeric.Endpoint40.profile0) := by
  have hraw : ThreeBoundNumeric.Endpoint40.RawNumericalBounds := by
    intro p
    fin_cases p
    · exact BS2_b3ba934b_Cert_40_RawNumerical0
    · exact BS2_b3ba934b_Cert_40_RawNumerical1
    · exact BS2_b3ba934b_Cert_40_RawNumerical2
    · exact BS2_b3ba934b_Cert_40_RawNumerical3
  exact ThreeBoundNumeric.Endpoint40.periodic_upper
    (ThreeBoundEndpoint40Campaign.raw_preserves_of_records BS2_b3ba934b_Cert_RecordsComplete) hraw
