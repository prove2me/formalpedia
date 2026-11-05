-- Prove2me | solution 1 for SelectedProfileCertificate.rational_gap_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/786be3cd-fdd1-4c36-add9-e63b970511df

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_SelectedProfileCertificate

set_option autoImplicit true
open SelectedProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SelectedProfileCertificate
theorem _root_.solution : 1 - rationalUpper = (23551960513937 / 4285993937500000000000000000000000000 : ℚ) := by decide +kernel
end SelectedProfileCertificate
