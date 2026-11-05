-- Prove2me | solution 1 for Pr73ProfileCertificate.rational_gap_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/bbb9719f-ed27-43b2-ba73-8b960d1d8bce

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_Pr73ProfileCertificate

set_option autoImplicit true
open Pr73ProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pr73ProfileCertificate
theorem _root_.solution : 1 - rationalUpper = (699597017858129667 / 4221114531250000000000000000000000000 : ℚ) := by decide +kernel
end Pr73ProfileCertificate
