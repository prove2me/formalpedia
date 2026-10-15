-- Prove2me | solution 1 for coefficients_scaled_product_vanish_below_degree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:45:57.380452+00:00
-- url     : https://prove2.me/submissions/4484286f-5837-4325-9f17-ef3f3ddf8f63

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Order

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (m : Fin n →₀ Nat)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D) :
    (∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (m.prod (fun i k => phi i ^ k)) = 0 := by
  classical
  intro hlt
  let d : Fin n →₀ Nat := Finsupp.equivFunOnFinite.symm e
  have hd : d.degree < D := by
    simpa [d, Finsupp.degree_eq_sum] using hlt
  have hz (i : Fin n) : (phi i).constantCoeff = 0 := by
    simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero i
  have horder (i : Fin n) : 1 ≤ (phi i).order :=
    (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero).2 (hz i)
  have hsumNat : D ≤ ∑ i ∈ m.support, m i := by
    rw [← hdeg]
    apply le_of_eq
    exact (Finset.sum_subset (Finset.subset_univ m.support) (by
      intro i hi hnot
      exact Finsupp.notMem_support_iff.mp hnot)).symm
  have hsumCast : (D : ℕ∞) ≤ ∑ i ∈ m.support, (m i : ℕ∞) := by
    exact_mod_cast hsumNat
  have hsumOrder :
      (D : ℕ∞) ≤ ∑ i ∈ m.support, (phi i ^ m i).order := by
    calc
      (D : ℕ∞) ≤ ∑ i ∈ m.support, (m i : ℕ∞) := hsumCast
      _ ≤ ∑ i ∈ m.support, (phi i ^ m i).order := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          (m i : ℕ∞) = m i • (1 : ℕ∞) := by simp
          _ ≤ m i • (phi i).order := by
            gcongr
            exact horder i
          _ ≤ (phi i ^ m i).order :=
            MvPowerSeries.le_order_pow (f := phi i) (m i)
  have hprod :
      (∑ i ∈ m.support, (phi i ^ m i).order) ≤
        (∏ i ∈ m.support, phi i ^ m i).order :=
    MvPowerSeries.le_order_prod (f := fun i : Fin n => phi i ^ m i) m.support
  have hfinal : d.degree < (m.prod fun i k => phi i ^ k).order := by
    apply lt_of_lt_of_le
      (show (d.degree : ℕ∞) < D from by exact_mod_cast hd)
    simpa only [Finsupp.prod] using le_trans hsumOrder hprod
  simpa [d] using MvPowerSeries.coeff_of_lt_order hfinal