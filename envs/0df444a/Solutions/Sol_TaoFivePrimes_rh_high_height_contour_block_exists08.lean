-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:40:50.733076+00:00
-- url     : https://prove2.me/submissions/4cef9d8a-1ac1-4256-a0fc-39b0d8091c8f

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Definitions.Def_TaoFivePrimes_RHHighContourCertificateV2Group08
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution : Nonempty (RHHighContourBlocks.Block 8192 256 (13581400043523159338086204868331027188070:Int)) := by
 exact ⟨{
  records := RHHighContourCertificateV2Group08.records
  length_eq := by decide +kernel
  coordinates_eq := by decide +kernel
  total_eq := by decide +kernel
 }⟩
#print axioms solution
