-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_first_chart_section_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T00:14:52.817284+00:00
-- url     : https://prove2.me/submissions/1abcd8a1-bee7-4622-a8a0-b0df5b35e4a3

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic


noncomputable section
namespace WeierstrassEllipticZeta

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def cubicSectionFamily (t x y u : A) (m n : ℕ)
    (a : Fin (m + 1) × Fin (2 * n + 1) × Fin 2 × Fin (4 * n + 1)) : A :=
  t ^ a.1.val * x ^ a.2.1.val * y ^ a.2.2.1.val * u ^ a.2.2.2.val

def cubicSectionSpan (t x y u : A) (m n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (cubicSectionFamily t x y u m n))

theorem weighted_monomial_mem_cubic_span (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n i j k l : ℕ) (hi : i ≤ m) (hw : 2 * j + 3 * k + l ≤ 4 * n) :
    t ^ i * x ^ j * y ^ k * u ^ l ∈ cubicSectionSpan t x y u m n := by
  induction k using Nat.twoStepInduction generalizing j with
  | zero =>
    exact Submodule.subset_span ⟨(⟨i, by omega⟩, ⟨j, by omega⟩, 0, ⟨l, by omega⟩), rfl⟩
  | one =>
    exact Submodule.subset_span ⟨(⟨i, by omega⟩, ⟨j, by omega⟩, 1, ⟨l, by omega⟩), rfl⟩
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
    exact (cubicSectionSpan t x y u m n).sub_mem
      ((cubicSectionSpan t x y u m n).sub_mem
        ((cubicSectionSpan t x y u m n).smul_mem 4 h₀)
        ((cubicSectionSpan t x y u m n).smul_mem g₂ h₁))
      ((cubicSectionSpan t x y u m n).smul_mem g₃ h₂)

end WeierstrassEllipticZeta


noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial
variable {A : Type*} [CommRing A] [Algebra ℂ A]

private theorem normalized_monomial_mem (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n : ℕ) (d : Fin 7 →₀ ℕ) (a : ℂ)
    (hm : d 0 + d 1 = m) (hn : d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] (monomial d a) ∈
      cubicSectionSpan t x y u m n := by
  classical
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.prod_empty, one_pow, one_mul, mul_one]
  change algebraMap ℂ A a * (t ^ d 1 * (x ^ d 3 * (y ^ d 4 *
    (u ^ d 5 * (y * u + 2 * x ^ 2) ^ d 6)))) ∈ _
  rw [add_pow]
  simp only [Finset.mul_sum]
  apply (cubicSectionSpan t x y u m n).sum_mem
  intro r hr
  have hrn : r ≤ d 6 := by simpa using hr
  have hmem := weighted_monomial_mem_cubic_span g₂ g₃ t x y u hy m n
    (d 1) (d 3 + 2 * (d 6 - r)) (d 4 + r) (d 5 + r) (by omega) (by omega)
  have hs := (cubicSectionSpan t x y u m n).smul_mem
    (a * 2 ^ (d 6 - r) * (Nat.choose (d 6) r : ℂ)) hmem
  convert hs using 1 <;>
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat, map_natCast,
      pow_add, mul_pow, pow_mul] <;> ring

theorem normalized_polynomial_mem_cubic_span (g₂ g₃ : ℂ) (t x y u : A)
    (hy : y ^ 2 = 4 * x ^ 3 - algebraMap ℂ A g₂ * x - algebraMap ℂ A g₃)
    (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q ∈
      cubicSectionSpan t x y u m n := by
  rw [Q.as_sum, map_sum]
  apply (cubicSectionSpan t x y u m n).sum_mem
  intro d hd
  exact normalized_monomial_mem g₂ g₃ t x y u hy m n d (coeff d Q) (hQ d hd).1 (hQ d hd).2

end WeierstrassEllipticZeta


noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial

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

private theorem section_space_le (L : PeriodPair) (m n : ℕ) :
    firstChartSectionSpace L m n ≤ cubicSectionSpan
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
  exact normalized_polynomial_mem_cubic_span L.g₂ L.g₃ _ _ _ _
    (quotient_cubic_relation L) m n Q hQ


end WeierstrassEllipticZeta

open TranscendenceTheory WeierstrassEllipticZeta MvPolynomial

theorem solution (L : PeriodPair) (m n : ℕ) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
      Module.finrank ℂ (firstChartSectionSpace L m n) ≤
        2 * (m + 1) * (2 * n + 1) * (4 * n + 1) ∧
      (1 ≤ n → Module.finrank ℂ (firstChartSectionSpace L m n) ≤
        30 * (m + 1) * n ^ 2) := by
  let t := firstCubicQuotient L (X 0)
  let x := firstCubicQuotient L (X 1)
  let y := firstCubicQuotient L (X 2)
  let u := firstCubicQuotient L (X 3)
  let V := cubicSectionSpan t x y u m n
  have hle : firstChartSectionSpace L m n ≤ V := section_space_le L m n
  letI : Module.Finite ℂ V := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  letI : Module.Finite ℂ (firstChartSectionSpace L m n) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hdimV : Module.finrank ℂ V ≤ 2 * (m + 1) * (2 * n + 1) * (4 * n + 1) := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range (cubicSectionFamily t x y u m n))) ≤ _
    calc
      _ ≤ Fintype.card (Fin (m + 1) × Fin (2 * n + 1) × Fin 2 × Fin (4 * n + 1)) :=
        finrank_range_le_card (R := ℂ) (cubicSectionFamily t x y u m n)
      _ = _ := by simp only [Fintype.card_prod, Fintype.card_fin]; ring
  have hdim := (Submodule.finrank_mono hle).trans hdimV
  refine ⟨inferInstance, hdim, ?_⟩
  intro hn
  apply hdim.trans
  calc
    2 * (m + 1) * (2 * n + 1) * (4 * n + 1) ≤
        2 * (m + 1) * (3 * n) * (5 * n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ = 30 * (m + 1) * n ^ 2 := by ring
