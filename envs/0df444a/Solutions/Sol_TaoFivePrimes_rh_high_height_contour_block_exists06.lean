-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists06
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:29:01.46571+00:00
-- url     : https://prove2.me/submissions/49b75caf-16ef-4366-83ce-8dc25e9d5d40

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Definitions.Def_TaoFivePrimes_RHHighContourCertificateV2Group06
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution : Nonempty (RHHighContourBlocks.Block 6144 1024 (109222057552147786244581392435653370580492:Int)) := by
 exact ⟨{
  records := RHHighContourCertificateV2Group06.records
  length_eq := by decide +kernel
  coordinates_eq := by decide +kernel
  total_eq := by decide +kernel
 }⟩
#print axioms solution
