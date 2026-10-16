-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:11:06.033723+00:00
-- url     : https://prove2.me/submissions/f8993791-3501-490f-bdf4-d887fa262498

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Definitions.Def_TaoFivePrimes_RHHighContourCertificateV2Group00
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution : Nonempty (RHHighContourBlocks.Block 0 1024 (109474726821181072649479699931489780124787:Int)) := by
 exact ⟨{
  records := RHHighContourCertificateV2Group00.records
  length_eq := by decide +kernel
  coordinates_eq := by decide +kernel
  total_eq := by decide +kernel
 }⟩
#print axioms solution
