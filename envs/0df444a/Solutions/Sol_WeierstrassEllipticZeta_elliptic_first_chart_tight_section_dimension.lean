-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_first_chart_tight_section_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T19:31:29.910559+00:00
-- url     : https://prove2.me/submissions/2607a9d7-7809-4ec2-810a-1c566485247f

import Definitions.Def_WeierstrassEllipticZeta_TightCubicSections
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_section_growth
import Mathlib.Tactic

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial
variable {A : Type*} [CommRing A] [Algebra ℂ A]

private theorem tight_weighted_monomial_mem (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n i j k l : ℕ) (hi : i ≤ m) (hl : l ≤ n) (hw : 2 * j + 3 * k + l ≤ 4 * n) :
    t ^ i * x ^ j * y ^ k * u ^ l ∈ tightCubicSectionSpan t x y u m n := by
  induction k using Nat.twoStepInduction generalizing j with
  | zero =>
    exact Submodule.subset_span ⟨(⟨i, by omega⟩,
      ⟨⟨l, by omega⟩, ⟨0, ⟨j, by dsimp; omega⟩⟩⟩), rfl⟩
  | one =>
    exact Submodule.subset_span ⟨(⟨i, by omega⟩,
      ⟨⟨l, by omega⟩, ⟨1, ⟨j, by dsimp; omega⟩⟩⟩), rfl⟩
  | more k ih _ =>
    have h₀ := ih (j + 3) (by omega)
    have h₁ := ih (j + 1) (by omega)
    have h₂ := ih j (by omega)
    have heq : t ^ i * x ^ j * y ^ (k + 2) * u ^ l =
        (4 : ℂ) • (t ^ i * x ^ (j + 3) * y ^ k * u ^ l) -
          g₂ • (t ^ i * x ^ (j + 1) * y ^ k * u ^ l) -
          g₃ • (t ^ i * x ^ j * y ^ k * u ^ l) := by
      rw [pow_add, hy]
      simp only [Algebra.smul_def, map_ofNat, pow_add]
      ring
    rw [heq]
    exact (tightCubicSectionSpan t x y u m n).sub_mem
      ((tightCubicSectionSpan t x y u m n).sub_mem
        ((tightCubicSectionSpan t x y u m n).smul_mem 4 h₀)
        ((tightCubicSectionSpan t x y u m n).smul_mem g₂ h₁))
      ((tightCubicSectionSpan t x y u m n).smul_mem g₃ h₂)

private theorem tight_normalized_monomial_mem (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n : ℕ) (d : Fin 7 →₀ ℕ) (a : ℂ)
    (hm : d 0 + d 1 = m) (hn : d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] (monomial d a) ∈
      tightCubicSectionSpan t x y u m n := by
  classical
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.prod_empty, one_pow, one_mul, mul_one]
  change algebraMap ℂ A a * (t ^ d 1 * (x ^ d 3 * (y ^ d 4 *
    (u ^ d 5 * (y * u + 2 * x ^ 2) ^ d 6)))) ∈ _
  rw [add_pow]
  simp only [Finset.mul_sum]
  apply (tightCubicSectionSpan t x y u m n).sum_mem
  intro r hr
  have hrn : r ≤ d 6 := by simpa using hr
  have hmem := tight_weighted_monomial_mem g₂ g₃ t x y u hy m n
    (d 1) (d 3 + 2 * (d 6 - r)) (d 4 + r) (d 5 + r) (by omega) (by omega) (by omega)
  have hs := (tightCubicSectionSpan t x y u m n).smul_mem
    (a * 2 ^ (d 6 - r) * (Nat.choose (d 6) r : ℂ)) hmem
  convert hs using 1 <;>
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat, map_natCast,
      pow_add, mul_pow, pow_mul] <;> ring

private theorem tight_normalized_polynomial_mem (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q ∈
      tightCubicSectionSpan t x y u m n := by
  rw [Q.as_sum, map_sum]
  apply (tightCubicSectionSpan t x y u m n).sum_mem
  intro d hd
  exact tight_normalized_monomial_mem g₂ g₃ t x y u hy m n d (coeff d Q) (hQ d hd).1 (hQ d hd).2

private theorem quotient_cubic_relation (L : PeriodPair) :
    firstCubicQuotient L (X 2) ^ 2 = 4 * firstCubicQuotient L (X 1) ^ 3 -
      algebraMap ℂ (FirstCubicCoordinateRing L) L.g₂ * firstCubicQuotient L (X 1) -
      algebraMap ℂ (FirstCubicCoordinateRing L) L.g₃ := by
  have hzero : firstCubicQuotient L (extensionChartCubic L.g₂ L.g₃ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hC (a : ℂ) : firstCubicQuotient L (C a) =
      algebraMap ℂ (FirstCubicCoordinateRing L) a := (firstCubicQuotient L).commutes a
  change firstCubicQuotient L (X 2 ^ 2 - C 4 * X 1 ^ 3 + C L.g₂ * X 1 + C L.g₃) = 0 at hzero
  simp only [map_add, map_sub, map_mul, map_pow,
    hC, map_ofNat] at hzero
  linear_combination hzero

private theorem tight_section_space_le (L : PeriodPair) (m n : ℕ) :
    firstChartSectionSpace L m n ≤ tightCubicSectionSpan
      (firstCubicQuotient L (X 0)) (firstCubicQuotient L (X 1))
      (firstCubicQuotient L (X 2)) (firstCubicQuotient L (X 3)) m n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨Q, hQ, rfl⟩
  have htwo : firstCubicQuotient L (C (2 : ℂ)) = (2 : FirstCubicCoordinateRing L) := by
    change firstCubicQuotient L (2 : MvPolynomial (Fin 4) ℂ) = 2
    exact map_ofNat _ _
  have hnorm : firstCubicQuotient L (extensionChartNormalize 0 Q) =
      aeval ![1, firstCubicQuotient L (X 0), 1, firstCubicQuotient L (X 1),
        firstCubicQuotient L (X 2), firstCubicQuotient L (X 3),
        firstCubicQuotient L (X 2) * firstCubicQuotient L (X 3) +
          2 * firstCubicQuotient L (X 1) ^ 2] Q := by
    rw [extensionChartNormalize, comp_aeval_apply]
    apply congrArg (fun f : Fin 7 → FirstCubicCoordinateRing L => aeval f Q)
    funext i
    fin_cases i <;> simp [extensionChartSubstitution, htwo]
  rw [hnorm]
  exact tight_normalized_polynomial_mem L.g₂ L.g₃ _ _ _ _
    (quotient_cubic_relation L) m n Q hQ

private theorem tight_index_card (m n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (TightCubicSectionIndex m n) =
      (m + 1) * ∑ c : Fin (n + 1), (4 * n - c.val) := by
  simp only [TightCubicSectionIndex, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  have hc := c.isLt
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  omega

private theorem tight_index_card_double (m n : ℕ) (hn : 1 ≤ n) :
    2 * Fintype.card (TightCubicSectionIndex m n) = 7 * (m + 1) * n * (n + 1) := by
  have hsum : (∑ c : Fin (n + 1), (4 * n - c.val)) +
      (∑ c : Fin (n + 1), c.val) = (n + 1) * (4 * n) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _c : Fin (n + 1), 4 * n := by
        apply Finset.sum_congr rfl
        intro c _
        have hc := c.isLt
        omega
      _ = _ := by simp
  have hid : (∑ c : Fin (n + 1), c.val) * 2 = (n + 1) * n := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j) (n + 1)]
    simpa using Finset.sum_range_id_mul_two (n + 1)
  have htwice : 2 * (∑ c : Fin (n + 1), (4 * n - c.val)) = 7 * n * (n + 1) := by
    nlinarith
  rw [tight_index_card m n hn]
  calc
    _ = (m + 1) * (2 * ∑ c : Fin (n + 1), (4 * n - c.val)) := by ring
    _ = _ := by rw [htwice]; ring


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta MvPolynomial

theorem solution (L : PeriodPair) (m n : ℕ)
    (hn : 1 ≤ n) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
    (m + 1) * (n + 1) ^ 2 ≤ Module.finrank ℂ (firstChartSectionSpace L m n) ∧
    2 * Module.finrank ℂ (firstChartSectionSpace L m n) ≤
      7 * (m + 1) * n * (n + 1) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ 7 * (m + 1) * n ^ 2 := by
  let t := firstCubicQuotient L (X 0)
  let x := firstCubicQuotient L (X 1)
  let y := firstCubicQuotient L (X 2)
  let u := firstCubicQuotient L (X 3)
  let V := tightCubicSectionSpan t x y u m n
  have hle : firstChartSectionSpace L m n ≤ V := tight_section_space_le L m n
  letI : Module.Finite ℂ V := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  letI : Module.Finite ℂ (firstChartSectionSpace L m n) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hdimV : Module.finrank ℂ V ≤ Fintype.card (TightCubicSectionIndex m n) :=
    finrank_range_le_card (R := ℂ) (tightCubicSectionFamily t x y u m n)
  have hdim := (Submodule.finrank_mono hle).trans hdimV
  have hdouble : 2 * Module.finrank ℂ (firstChartSectionSpace L m n) ≤
      7 * (m + 1) * n * (n + 1) := by
    rw [← tight_index_card_double m n hn]
    exact Nat.mul_le_mul_left 2 hdim
  refine ⟨inferInstance, (elliptic_first_chart_section_growth L m n).2.1, hdouble, ?_⟩
  have hu : 7 * (m + 1) * n * (n + 1) ≤ 2 * (7 * (m + 1) * n ^ 2) := by
    calc
      _ ≤ 7 * (m + 1) * n * (2 * n) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have := hdouble.trans hu
  omega
