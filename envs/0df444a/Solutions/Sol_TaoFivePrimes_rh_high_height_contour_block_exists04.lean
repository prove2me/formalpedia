-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:21:24.336514+00:00
-- url     : https://prove2.me/submissions/61c2aaef-da08-4bf0-ad22-0856298c5fc1

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Definitions.Def_TaoFivePrimes_RHHighContourCertificateV2Group04
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution : Nonempty (RHHighContourBlocks.Block 4096 1024 (95347179568355145696770173980499915190313:Int)) := by
 exact ⟨{
  records := RHHighContourCertificateV2Group04.records
  length_eq := by decide +kernel
  coordinates_eq := by decide +kernel
  total_eq := by decide +kernel
 }⟩
#print axioms solution
