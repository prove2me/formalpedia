-- Prove2me | solution 1 for coefficients_scaled_product_degree_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:45:20.878987+00:00
-- url     : https://prove2.me/submissions/2e714ef3-46fa-4f91-a52f-94f89e874dbe

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_mvPowerSeries_homogeneousComponent_finsuppProd_of_constantCoeff_zero

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (m : Fin n →₀ Nat)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D) :
    (∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (m.prod (fun i k => phi i ^ k)) =
          (if m = Finsupp.equivFunOnFinite.symm e then 1 else 0) := by
  classical
  intro hedeg
  have hc (i : Fin n) : MvPowerSeries.constantCoeff (phi i) = 0 := by
    simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero i
  have hfirst (i : Fin n) :
      MvPowerSeries.homogeneousComponent 1 (phi i) = MvPowerSeries.X i := by
    apply MvPowerSeries.ext
    intro d
    rw [MvPowerSeries.coeff_homogeneousComponent]
    by_cases hd : d.degree = 1
    · rw [if_pos hd]
      have hd' : d ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
        rw [Finsupp.range_single_one]
        exact hd
      obtain ⟨j, rfl⟩ := hd'
      simpa only [MvPowerSeries.coeff_index_single_X, eq_comm] using hlinear i j
    · have hne : d ≠ Finsupp.single i 1 := by
        intro h
        apply hd
        rw [h, Finsupp.degree_single]
      rw [if_neg hd, MvPowerSeries.coeff_X, if_neg hne]
  have hmdeg : m.degree = D := by
    rw [Finsupp.degree_eq_sum]
    exact hdeg
  have hedeg' : (Finsupp.equivFunOnFinite.symm e).degree = D := by
    rw [Finsupp.degree_eq_sum]
    exact hedeg
  have hb := congrArg (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e))
    (mvPowerSeries_homogeneousComponent_finsuppProd_of_constantCoeff_zero phi hc m)
  rw [MvPowerSeries.coeff_homogeneousComponent, hmdeg, hedeg', if_pos rfl] at hb
  rw [hb]
  simp_rw [hfirst]
  rw [← MvPowerSeries.monomial_one_eq, MvPowerSeries.coeff_monomial]
  simp only [eq_comm]