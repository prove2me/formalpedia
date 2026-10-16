-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:20:53.436983+00:00
-- url     : https://prove2.me/submissions/eedc5710-0ae5-4e24-a18f-b8aa0dbd032f

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Definitions.Def_TaoFivePrimes_RHHighContourCertificateV2Group03
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution : Nonempty (RHHighContourBlocks.Block 3072 1024 (109023063714152716956520007734775178844209:Int)) := by
 exact ⟨{
  records := RHHighContourCertificateV2Group03.records
  length_eq := by decide +kernel
  coordinates_eq := by decide +kernel
  total_eq := by decide +kernel
 }⟩
#print axioms solution
