-- Prove2me | solution 1 for SelectedProfileReal.log_two_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/863fbdc3-2fa1-4380-a009-4f61da81000d

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_SelectedProfileReal
import Theorems.Thm_AnalyticEnclosures_log_le_of_expPoly
import Theorems.Thm_SelectedProfileCertificate_logTwo_certificate


set_option autoImplicit true
open SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate
namespace SelectedProfileReal
theorem _root_.solution : Real.log 2 ≤ (logTwoUpper : ℝ) := by
  simpa using log_le_of_expPoly 2 logTwoUpper 24 (by decide)
    logTwo_certificate.1 logTwo_certificate.2
end SelectedProfileReal
