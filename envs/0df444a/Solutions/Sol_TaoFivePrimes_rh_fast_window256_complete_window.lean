-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_complete_window
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:47:18.698513+00:00
-- url     : https://prove2.me/submissions/ab813a59-63ac-419e-8f02-e8fdc0a05cbb

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_window_from_gamma_bounds
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_all_gamma_fourier_enclosures
set_option Elab.async false

theorem solution : ∀s∈RHHighHeight.windowZeros 3289999872 3290000000,s.re=1/2 := by
 exact TaoFivePrimes.rh_fast_window256_window_from_gamma_bounds
  TaoFivePrimes.rh_fast_window256_all_gamma_fourier_enclosures
#print axioms solution
