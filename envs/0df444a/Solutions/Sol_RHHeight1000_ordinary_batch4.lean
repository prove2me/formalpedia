-- Prove2me | solution 1 for RHHeight1000.ordinary_batch4
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-26T15:43:25.664057+00:00
-- url     : https://prove2.me/submissions/86a48e68-8851-4ae4-9b8d-588262e26893

import Theorems.Thm_RHHeight1000_ordinary_batch4_inline_tail

theorem solution : Zeta.Certificates.BatchSpec 4 1004192 1000 1008988 1000 :=
  RHHeight1000.ordinary_batch4_inline_tail