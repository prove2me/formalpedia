-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.inv_sqrt_eight_lt_one_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/af1f509b-3c0c-4443-b7c1-7ee1a5e6460e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution :
    (Real.sqrt (8 : ℝ))⁻¹ < (1 / 2 : ℝ) := by
  have hsqrt : 2 < Real.sqrt (8 : ℝ) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
    have hnonneg := Real.sqrt_nonneg (8 : ℝ)
    nlinarith
  simpa [one_div] using
    (one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num) hsqrt)
end SoficGroups.ErshovJaikinFiniteSpectral
