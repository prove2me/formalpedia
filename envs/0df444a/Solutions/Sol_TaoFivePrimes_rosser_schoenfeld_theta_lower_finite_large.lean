-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:27:49.79392+00:00
-- url     : https://prove2.me/submissions/7e78ee28-27a4-4777-b0fb-9810dff0f9b5

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_low
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_mid
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high

open TaoFivePrimes

theorem solution (t : Real) (h1 : 1423 <= t) (h2 : t <= 10 ^ 8) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by
  rcases le_total t (10 ^ 4) with hlow | hlow
  · exact rosser_schoenfeld_theta_lower_finite_large_low t h1 hlow
  · rcases le_total t (10 ^ 6) with hmid | hmid
    · exact rosser_schoenfeld_theta_lower_finite_large_mid t hlow hmid
    · exact rosser_schoenfeld_theta_lower_finite_large_high t hmid h2
