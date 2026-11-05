-- Prove2me | solution 1 for Pr73ProfileCertificate.logTwo_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/e1396d25-006e-444f-a5f6-97530e5ccfd5

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_Pr73ProfileCertificate

set_option autoImplicit true
open Pr73ProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pr73ProfileCertificate
theorem _root_.solution : 0 ≤ logTwoUpper ∧ (2 : ℚ) ≤ expPoly logTwoUpper 24 := by decide +kernel
end Pr73ProfileCertificate
