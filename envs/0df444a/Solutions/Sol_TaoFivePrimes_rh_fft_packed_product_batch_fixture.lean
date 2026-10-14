-- Prove2me | solution 1 for TaoFivePrimes.rh_fft_packed_product_batch_fixture
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T09:30:07.391007+00:00
-- url     : https://prove2.me/submissions/8979a521-f728-4d6f-9855-d7083d8ea1e4

import Definitions.Def_TaoFivePrimes_RHFFT4096PackedFixture
import Theorems.Thm_TaoFivePrimes_rh_certificate_fastMul_correct
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open RHFFT4096PackedFixture
attribute [local irreducible] RHScalableArithmetic.fastMul
theorem checked : ∀ i : Fin 16, RHScalableArithmetic.fastMul 4 288730 (a+i.val) b=c+i.val*b := by
  decide +kernel
theorem solution (i : Fin 16) : (a+i.val)*b=c+i.val*b :=
  (TaoFivePrimes.rh_certificate_fastMul_correct 4 288730 (a+i.val) b).symm.trans (checked i)
