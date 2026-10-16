-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:15:36.725305+00:00
-- url     : https://prove2.me/submissions/7918aff1-4115-4045-9a71-347f738c5422

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Definitions.Def_TaoFivePrimes_RHHighContourCertificateV2Group01
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution : Nonempty (RHHighContourBlocks.Block 1024 1024 (109311968457341044839389112112005514116770:Int)) := by
 exact ⟨{
  records := RHHighContourCertificateV2Group01.records
  length_eq := by decide +kernel
  coordinates_eq := by decide +kernel
  total_eq := by decide +kernel
 }⟩
#print axioms solution
