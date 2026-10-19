-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_packed_reference_equality
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:00:05.527987+00:00
-- url     : https://prove2.me/submissions/ea5d6a59-35d8-40a7-ac00-53d35b2ca41a

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem solution :
 (List.range 24).map (fun k=>(List.range 2048).map (RHFastWindow256CompactReference.raw k))=
  RHHighGammaFourierTable.packets := by decide +kernel
#print axioms solution
