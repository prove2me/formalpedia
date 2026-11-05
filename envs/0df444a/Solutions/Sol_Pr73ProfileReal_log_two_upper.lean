-- Prove2me | solution 1 for Pr73ProfileReal.log_two_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/f9d49af3-f521-40ae-b17b-c1639d4d1675

import Definitions.Def_Pr73ProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Pr73ProfileReal
import Theorems.Thm_AnalyticEnclosures_log_le_of_expPoly
import Theorems.Thm_Pr73ProfileCertificate_logTwo_certificate


set_option autoImplicit true
open Pr73ProfileReal
open AnalyticEnclosures Pr73ProfileCertificate
namespace Pr73ProfileReal
theorem _root_.solution : Real.log 2 ≤ (logTwoUpper : ℝ) := by
  simpa using log_le_of_expPoly 2 logTwoUpper 24 (by decide)
    logTwo_certificate.1 logTwo_certificate.2
end Pr73ProfileReal
