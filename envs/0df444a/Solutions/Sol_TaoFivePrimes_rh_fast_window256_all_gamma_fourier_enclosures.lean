-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_all_gamma_fourier_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:42:41.486819+00:00
-- url     : https://prove2.me/submissions/a7dbaff0-764b-4f02-b95d-8e1c7f88f5c4

import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_frequency_enclosure_from_checked
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_all_arithmetic_checked
set_option Elab.async false
open scoped FourierTransform

theorem solution (k j:Nat) (hk:k<24) (hj:j<1954) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537 := by
 exact TaoFivePrimes.rh_fast_window256_frequency_enclosure_from_checked k j hk hj
  (TaoFivePrimes.rh_fast_window256_all_arithmetic_checked j hj)
#print axioms solution
