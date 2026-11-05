-- Prove2me | solution 1 for SelectedProfileCertificate.logTwo_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/7f92c02c-feff-49d9-8cb5-549ce6105a3b

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_SelectedProfileCertificate

set_option autoImplicit true
open SelectedProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SelectedProfileCertificate
theorem _root_.solution : 0 ≤ logTwoUpper ∧ (2 : ℚ) ≤ expPoly logTwoUpper 24 := by decide +kernel
end SelectedProfileCertificate
