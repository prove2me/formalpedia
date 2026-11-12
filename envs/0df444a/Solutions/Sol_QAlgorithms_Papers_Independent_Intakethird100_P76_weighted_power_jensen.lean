-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P76.weighted_power_jensen
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:49:26.193068+00:00
-- url     : https://prove2.me/submissions/52d31b2a-26d3-4e37-b831-90443764cce8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

theorem solution {J : Type*} [Fintype J] (weights values : J → ℝ)
    (hweights : ∀ j, 0 ≤ weights j) (hvalues : ∀ j, 0 ≤ values j)
    (hsum : ∑ j, weights j = 1) (r : ℝ) (hr : 1 ≤ r) :
    (∑ j, weights j * values j) ^ r ≤ ∑ j, weights j * (values j) ^ r := by
  have h := (convexOn_rpow hr).map_sum_le (t := Finset.univ) (w := weights) (p := values)
    (fun j _ => hweights j) hsum (fun j _ => Set.mem_Ici.mpr (hvalues j))
  simp only [smul_eq_mul] at h
  exact h
