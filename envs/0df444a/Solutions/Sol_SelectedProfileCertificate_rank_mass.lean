-- Prove2me | solution 1 for SelectedProfileCertificate.rank_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/dbd18828-3c33-4812-b44a-0c677d02a4c4

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_SelectedProfileCertificate

set_option autoImplicit true
open SelectedProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SelectedProfileCertificate
theorem _root_.solution : (rows.map (fun r => r.width * r.multiplicity)).sum = 78860441550 := by decide +kernel
end SelectedProfileCertificate
