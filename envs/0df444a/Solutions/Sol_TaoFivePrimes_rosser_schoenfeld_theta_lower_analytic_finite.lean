-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:56:40.775104+00:00
-- url     : https://prove2.me/submissions/6e6cbfcc-23f1-43b6-a491-f99757b3fc95

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite_low
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite_mid
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite_high

open TaoFivePrimes

theorem solution (t : Real) (h1 : 1420 <= t) (h2 : t <= 10 ^ 8) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  rcases le_total t (10 ^ 4) with hlow | hlow
  · exact rosser_schoenfeld_theta_lower_analytic_finite_low t h1 hlow
  · rcases le_total t (10 ^ 6) with hmid | hmid
    · exact rosser_schoenfeld_theta_lower_analytic_finite_mid t hlow hmid
    · exact rosser_schoenfeld_theta_lower_analytic_finite_high t hmid h2