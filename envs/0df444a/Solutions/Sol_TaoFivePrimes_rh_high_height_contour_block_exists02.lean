-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:15:51.178195+00:00
-- url     : https://prove2.me/submissions/38f2471a-822e-46d8-9ff8-d3f1e7c49222

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Definitions.Def_TaoFivePrimes_RHHighContourCertificateV2Group02
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution : Nonempty (RHHighContourBlocks.Block 2048 1024 (109571840244712964494502534988015572730856:Int)) := by
 exact ⟨{
  records := RHHighContourCertificateV2Group02.records
  length_eq := by decide +kernel
  coordinates_eq := by decide +kernel
  total_eq := by decide +kernel
 }⟩
#print axioms solution
