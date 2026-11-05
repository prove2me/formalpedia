-- Prove2me | solution 1 for Pr73ProfileCertificate.rank_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/d63c553c-8cb1-40ae-9352-628881b15933

import Definitions.Def_AnalyticEnclosures
import Definitions.Def_Pr73ProfileCertificate

set_option autoImplicit true
open Pr73ProfileCertificate
open AnalyticEnclosures
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Pr73ProfileCertificate
theorem _root_.solution : (rows.map (fun r => r.width * r.multiplicity)).sum = 77666660475 := by decide +kernel
end Pr73ProfileCertificate
