-- Prove2me | solution 1 for coefficients_product_of_coordinate_variables
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:12:13.388003+00:00
-- url     : https://prove2.me/submissions/d154d37b-9173-4ca9-a0b9-dfdfa2864c77

import Mathlib
set_option autoImplicit false

theorem solution
    {n : Nat}
    (m : Fin n →₀ Nat)
    (e : Fin n → Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (m.prod (fun i k => MvPowerSeries.X i ^ k)) =
    (if m = Finsupp.equivFunOnFinite.symm e then 1 else 0) := by
  rw [← MvPowerSeries.monomial_one_eq, MvPowerSeries.coeff_monomial]
  by_cases h : m = Finsupp.equivFunOnFinite.symm e
  · simp [h]
  · simp [h, Ne.symm h]
