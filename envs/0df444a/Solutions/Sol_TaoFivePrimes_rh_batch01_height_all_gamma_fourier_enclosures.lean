-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_all_gamma_fourier_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T18:03:32.474607+00:00
-- url     : https://prove2.me/submissions/d4913ef9-1c73-46b6-888c-d796fcd1c578

import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_frequency_enclosure_from_checked
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_all_arithmetic_checked
set_option Elab.async false
open scoped FourierTransform

theorem solution (k j:Nat) (hk:k<24) (hj:j<1954) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)-RHBatch01GammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)‖≤65537 := by
 exact TaoFivePrimes.rh_batch01_new256_frequency_enclosure_from_checked k j hk hj
  (TaoFivePrimes.rh_batch01_new256_all_arithmetic_checked j hj)
#print axioms solution
