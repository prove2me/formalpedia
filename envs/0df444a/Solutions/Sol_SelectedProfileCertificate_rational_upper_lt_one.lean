-- Prove2me | solution 1 for SelectedProfileCertificate.rational_upper_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/1e3bdd05-77f6-4ab2-a55c-26bcb9f3a487

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_SelectedProfileCertificate

set_option autoImplicit true
open SelectedProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SelectedProfileCertificate
theorem _root_.solution : rationalUpper < 1 := by decide +kernel
end SelectedProfileCertificate
