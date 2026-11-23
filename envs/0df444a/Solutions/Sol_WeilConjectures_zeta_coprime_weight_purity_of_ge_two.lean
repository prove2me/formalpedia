-- Prove2me | solution 1 for WeilConjectures.zeta_coprime_weight_purity_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:52:27.160791+00:00
-- url     : https://prove2.me/submissions/d507dfcb-c35d-4287-9ff9-f76dc4489a26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_pure_weil_zeta_factorization_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section WeightPurityFromFactorization

private lemma reverse_prod_of_domain {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    (∏ i ∈ s, f i).reverse = ∏ i ∈ s, (f i).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, ← Polynomial.C_1, Polynomial.reverse_C]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.reverse_mul_of_domain, ih]

private lemma reverse_one_sub_X : (1 - Polynomial.X : ℚ[X]).reverse = Polynomial.X - 1 := by
  have hdeg : (1 - Polynomial.X : ℚ[X]).natDegree = 1 := by
    have h1 : (1 - Polynomial.X : ℚ[X]) = -(Polynomial.X - Polynomial.C 1) := by
      rw [map_one]; ring
    rw [h1, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  ext m
  rw [Polynomial.coeff_reverse, hdeg]
  rcases m with _ | _ | m
  · simp [Polynomial.revAt_le, Polynomial.coeff_one]
  · simp [Polynomial.revAt_le, Polynomial.coeff_one]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega : 1 < m + 2)]
    simp [Polynomial.coeff_X, Polynomial.coeff_one]

private lemma aeval_eq_zero_of_dvd {r Q : ℚ[X]} (hdvd : r ∣ Q) {z : ℂ}
    (hr : aeval z r = 0) : aeval z Q = 0 := by
  rcases hdvd with ⟨u, rfl⟩
  rw [map_mul, hr, zero_mul]

end WeightPurityFromFactorization

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (N D : ℚ[X]) (hcop : IsCoprime N D) (hN0 : N.coeff 0 = 1) (hD0 : D.coeff 0 = 1)
    (hzeta : zetaFunction p f * (D : PowerSeries ℚ) = (N : PowerSeries ℚ)) :
    (Polynomial.X - 1 ∣ D.reverse) ∧
    (∀ r : ℚ[X], Irreducible r → r ∣ D.reverse / (Polynomial.X - 1) →
      ∃ i ≤ 2 * n, Even i ∧ 0 < i ∧
        ∀ z : ℂ, aeval z r = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) ∧
    (∀ r : ℚ[X], Irreducible r → r ∣ N.reverse →
      ∃ i ≤ 2 * n, Odd i ∧
        ∀ z : ℂ, aeval z r = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  have _ := hN0
  have _ := hD0
  obtain ⟨P, hP0, _, hPzeta, hPnorm⟩ :=
    WeilConjectures.exists_pure_weil_zeta_factorization_of_ge_two p k n hn X f hproj
  let sEven : Finset ℕ := (Finset.range (2 * n + 1)).filter Even
  let sOdd : Finset ℕ := (Finset.range (2 * n + 1)).filter Odd
  let D' : ℚ[X] := ∏ i ∈ sEven, P i
  let N' : ℚ[X] := ∏ i ∈ sOdd, P i
  have hD'_ps : (D' : PowerSeries ℚ) = ∏ i ∈ sEven, (P i : PowerSeries ℚ) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) P sEven
  have hN'_ps : (N' : PowerSeries ℚ) = ∏ i ∈ sOdd, (P i : PowerSeries ℚ) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) P sOdd
  have hPzeta' : zetaFunction p f * (D' : PowerSeries ℚ) = (N' : PowerSeries ℚ) := by
    rw [hD'_ps, hN'_ps]
    exact hPzeta
  have hND'_ps : ((N * D' : ℚ[X]) : PowerSeries ℚ) = ((N' * D : ℚ[X]) : PowerSeries ℚ) := by
    calc
      ((N * D' : ℚ[X]) : PowerSeries ℚ)
          = (N : PowerSeries ℚ) * (D' : PowerSeries ℚ) := Polynomial.coe_mul N D'
      _ = (zetaFunction p f * (D : PowerSeries ℚ)) * (D' : PowerSeries ℚ) := by rw [hzeta]
      _ = (zetaFunction p f * (D' : PowerSeries ℚ)) * (D : PowerSeries ℚ) := by ring
      _ = (N' : PowerSeries ℚ) * (D : PowerSeries ℚ) := by rw [hPzeta']
      _ = ((N' * D : ℚ[X]) : PowerSeries ℚ) := (Polynomial.coe_mul N' D).symm
  have hND' : N * D' = N' * D := Polynomial.coe_injective (R := ℚ) hND'_ps
  have hD_dvd : D ∣ D' :=
    hcop.symm.dvd_of_dvd_mul_left ⟨N', by rw [hND', mul_comm]⟩
  have hN_dvd : N ∣ N' := hcop.dvd_of_dvd_mul_right ⟨D', by rw [hND', mul_comm]⟩
  have hDrev_dvd : D.reverse ∣ D'.reverse := by
    rcases hD_dvd with ⟨u, hu⟩
    exact ⟨u.reverse, by rw [hu, Polynomial.reverse_mul_of_domain]⟩
  have hNrev_dvd : N.reverse ∣ N'.reverse := by
    rcases hN_dvd with ⟨v, hv⟩
    exact ⟨v.reverse, by rw [hv, Polynomial.reverse_mul_of_domain]⟩
  have hD'rev_eq : D'.reverse = ∏ i ∈ sEven, (P i).reverse := reverse_prod_of_domain sEven P
  have hN'rev_eq : N'.reverse = ∏ i ∈ sOdd, (P i).reverse := reverse_prod_of_domain sOdd P
  have h0_mem : 0 ∈ sEven := by simp [sEven]
  have hD'rev_split :
      D'.reverse = (Polynomial.X - 1) * ∏ i ∈ sEven.erase 0, (P i).reverse := by
    rw [hD'rev_eq, ← Finset.mul_prod_erase sEven (fun i => (P i).reverse) h0_mem,
      hP0, reverse_one_sub_X]
  have hX1_irred : Irreducible (Polynomial.X - 1 : ℚ[X]) := by
    simpa [map_one] using Polynomial.irreducible_X_sub_C (1 : ℚ)
  have hX1_prime : Prime (Polynomial.X - 1 : ℚ[X]) := hX1_irred.prime
  have hX1_ne : (Polynomial.X - 1 : ℚ[X]) ≠ 0 := hX1_prime.ne_zero
  have hq_gt1 : (1 : ℝ) < (Nat.card k : ℝ) := by
    exact_mod_cast Finite.one_lt_card (α := k)
  have hnot_X1_dvd_N' : ¬ (Polynomial.X - 1 ∣ N'.reverse) := by
    intro hdvd
    rw [hN'rev_eq] at hdvd
    obtain ⟨i, hi_mem, hi_dvd⟩ := (hX1_prime.dvd_finsetProd_iff _).mp hdvd
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi_mem).1)
    have hi_odd : Odd i := (Finset.mem_filter.mp hi_mem).2
    have hi_pos : (0 : ℝ) < (i : ℝ) / 2 := by
      rcases hi_odd with ⟨m, rfl⟩
      positivity
    have hroot1 : aeval (1 : ℂ) (P i).reverse = 0 :=
      aeval_eq_zero_of_dvd hi_dvd (by simp)
    have hnorm1 : ‖(1 : ℂ)‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2) :=
      hPnorm i hi_le 1 hroot1
    have hgt : (1 : ℝ) < (Nat.card k : ℝ) ^ ((i : ℝ) / 2) := Real.one_lt_rpow hq_gt1 hi_pos
    rw [norm_one] at hnorm1
    linarith
  have hX1_dvd_Drev : Polynomial.X - 1 ∣ D.reverse := by
    have hrev_eq : N.reverse * D'.reverse = N'.reverse * D.reverse := by
      have := congrArg Polynomial.reverse hND'
      rwa [Polynomial.reverse_mul_of_domain, Polynomial.reverse_mul_of_domain] at this
    have hdvd_prod : Polynomial.X - 1 ∣ N'.reverse * D.reverse := by
      rw [← hrev_eq, hD'rev_split]
      exact ⟨N.reverse * ∏ i ∈ sEven.erase 0, (P i).reverse, by ring⟩
    exact (hX1_prime.dvd_or_dvd hdvd_prod).resolve_left hnot_X1_dvd_N'
  refine ⟨hX1_dvd_Drev, ?_, ?_⟩
  · intro r hr_irred hr_dvd
    have hquot_dvd : D.reverse / (Polynomial.X - 1) ∣ ∏ i ∈ sEven.erase 0, (P i).reverse := by
      have hmul_dvd :
          (Polynomial.X - 1) * (D.reverse / (Polynomial.X - 1)) ∣
            (Polynomial.X - 1) * ∏ i ∈ sEven.erase 0, (P i).reverse := by
        rw [EuclideanDomain.mul_div_cancel' hX1_ne hX1_dvd_Drev, ← hD'rev_split]
        exact hDrev_dvd
      exact (mul_dvd_mul_iff_left hX1_ne).mp hmul_dvd
    obtain ⟨i, hi_mem, hi_dvd⟩ :=
      (hr_irred.prime.dvd_finsetProd_iff _).mp (dvd_trans hr_dvd hquot_dvd)
    have hi_ne0 : i ≠ 0 := (Finset.mem_erase.mp hi_mem).1
    have hi_sEven : i ∈ sEven := (Finset.mem_erase.mp hi_mem).2
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi_sEven).1)
    have hi_even : Even i := (Finset.mem_filter.mp hi_sEven).2
    refine ⟨i, hi_le, hi_even, Nat.pos_of_ne_zero hi_ne0, ?_⟩
    intro z hz
    exact hPnorm i hi_le z (aeval_eq_zero_of_dvd hi_dvd hz)
  · intro r hr_irred hr_dvd
    have hr_prod : r ∣ ∏ i ∈ sOdd, (P i).reverse := by
      rw [← hN'rev_eq]
      exact dvd_trans hr_dvd hNrev_dvd
    obtain ⟨i, hi_mem, hi_dvd⟩ := (hr_irred.prime.dvd_finsetProd_iff _).mp hr_prod
    have hi_le : i ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi_mem).1)
    have hi_odd : Odd i := (Finset.mem_filter.mp hi_mem).2
    refine ⟨i, hi_le, hi_odd, ?_⟩
    intro z hz
    exact hPnorm i hi_le z (aeval_eq_zero_of_dvd hi_dvd hz)
