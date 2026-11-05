-- Prove2me | solution 1 for Pr73ProfileCertificate.rational_upper_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/19a4211f-eaa5-44a3-882e-62a4288d5a71

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_Pr73ProfileCertificate

set_option autoImplicit true
open Pr73ProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pr73ProfileCertificate
theorem _root_.solution : rationalUpper < 1 := by decide +kernel
end Pr73ProfileCertificate
