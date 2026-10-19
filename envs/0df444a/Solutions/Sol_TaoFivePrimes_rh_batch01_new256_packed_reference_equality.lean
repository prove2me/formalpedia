-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_packed_reference_equality
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:41:19.880351+00:00
-- url     : https://prove2.me/submissions/c63d3cf3-1cdf-4ca2-839f-b73c09754203

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution :
 (List.range 24).map (fun k=>(List.range 2048).map (RHBatch01New256CompactReference.raw k))=
  RHBatch01GammaFourierTable.packets := by decide +kernel
#print axioms solution
