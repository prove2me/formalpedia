-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_window_from_gamma_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:37:30.681913+00:00
-- url     : https://prove2.me/submissions/4df95bb8-46fd-42b0-ab95-f6012af2222c

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_coefficient_from_gamma_bounds
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_signs_from_coefficients
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_count_from_coefficients_and_jets
import Theorems.Thm_TaoFivePrimes_rh_high_height_all_contour_jets
import Theorems.Thm_TaoFivePrimes_rh_high_height_window_of_signs_and_count
set_option Elab.async false
set_option maxHeartbeats 1000000
open scoped FourierTransform

theorem solution
 (hgamma:∀k j:Nat,k<24 → j<1954 →
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537) :
 ∀s∈RHHighHeight.windowZeros 3289999872 3290000000,s.re=1/2 := by
 have hc:=TaoFivePrimes.rh_fast_window256_coefficient_from_gamma_bounds hgamma
 have hs:=TaoFivePrimes.rh_fast_window256_signs_from_coefficients hc
 have hn:=TaoFivePrimes.rh_fast_window256_count_from_coefficients_and_jets hc
  (fun e j k he hj hk=>TaoFivePrimes.rh_high_height_all_contour_jets e j k he hj hk)
 exact TaoFivePrimes.rh_high_height_window_of_signs_and_count hs hn
#print axioms solution
