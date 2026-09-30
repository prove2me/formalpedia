-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_first_chart_birelation_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T21:18:14.573866+00:00
-- url     : https://prove2.me/submissions/0d1c26f2-0713-4222-8524-573ccacfa0d2

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Mathlib.Tactic

noncomputable section
open scoped Classical
open MvPolynomial
namespace WeierstrassEllipticZeta

private abbrev SectionIndex (m n : ℕ) :=
  Fin (m + 1) × (Σ a : Fin (min 2 n + 1),
    Fin (n - a.val + 1) × Fin (n - a.val + 1))

private def sectionFamily {A : Type*} [CommRing A]
    (t x y u w : A) (m n : ℕ) (s : SectionIndex m n) : A :=
  t ^ s.1.val * x ^ s.2.1.val * y ^ (s.2.2.1.val - s.2.2.2.val) *
    u ^ (s.2.2.2.val - s.2.2.1.val) * w ^ min s.2.2.1.val s.2.2.2.val

private def sectionSpan {A : Type*} [CommRing A] [Algebra ℂ A]
    (t x y u w : A) (m n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (sectionFamily t x y u w m n))

variable {A : Type*} [CommRing A] [Algebra ℂ A]

private lemma normal_monomial_mem (t x y u w : A) (m n i j k l r : ℕ)
    (hi : i ≤ m) (hj : j ≤ 2) (hkl : k = 0 ∨ l = 0) (hdeg : j + k + l + r ≤ n) :
    t ^ i * x ^ j * y ^ k * u ^ l * w ^ r ∈ sectionSpan t x y u w m n := by
  let s : SectionIndex m n := (⟨i, by omega⟩,
    ⟨⟨j, by omega⟩, ⟨⟨k + r, by change k + r < n - j + 1; omega⟩,
      ⟨l + r, by change l + r < n - j + 1; omega⟩⟩⟩)
  refine Submodule.subset_span ⟨s, ?_⟩
  rcases hkl with rfl | rfl <;>
    simp [sectionFamily, s]

private lemma all_monomial_mem (g₂ g₃ : ℂ) (t x y u w : A)
    (hx : x ^ 3 = (1 / 4 : ℂ) • y ^ 2 + (g₂ / 4) • x + (g₃ / 4) • (1 : A))
    (hw : y * u = w - 2 * x ^ 2)
    (m n i j k l r : ℕ) (hi : i ≤ m) (hdeg : j + k + l + r ≤ n) :
    t ^ i * x ^ j * y ^ k * u ^ l * w ^ r ∈ sectionSpan t x y u w m n := by
  generalize hs : 2 * j + 2 * k + 3 * l = s
  induction s using Nat.strong_induction_on generalizing j k l r with
  | h s ih =>
    have hsmaller (j' k' l' r' : ℕ) (hlt : 2 * j' + 2 * k' + 3 * l' < s)
        (hd : j' + k' + l' + r' ≤ n) :
        t ^ i * x ^ j' * y ^ k' * u ^ l' * w ^ r' ∈ sectionSpan t x y u w m n :=
      ih _ hlt j' k' l' r' hd rfl
    by_cases hj : 3 ≤ j
    · obtain ⟨a, rfl⟩ : ∃ a, j = a + 3 := ⟨j - 3, by omega⟩
      have h₀ := hsmaller a (k + 2) l r (by omega) (by omega)
      have h₁ := hsmaller (a + 1) k l r (by omega) (by omega)
      have h₂ := hsmaller a k l r (by omega) (by omega)
      have heq : t ^ i * x ^ (a + 3) * y ^ k * u ^ l * w ^ r =
          (1 / 4 : ℂ) • (t ^ i * x ^ a * y ^ (k + 2) * u ^ l * w ^ r) +
          (g₂ / 4) • (t ^ i * x ^ (a + 1) * y ^ k * u ^ l * w ^ r) +
          (g₃ / 4) • (t ^ i * x ^ a * y ^ k * u ^ l * w ^ r) := by
        rw [pow_add, hx]
        simp only [Algebra.smul_def, pow_add]
        ring
      rw [heq]
      exact (sectionSpan t x y u w m n).add_mem
        ((sectionSpan t x y u w m n).add_mem
          ((sectionSpan t x y u w m n).smul_mem _ h₀)
          ((sectionSpan t x y u w m n).smul_mem _ h₁))
        ((sectionSpan t x y u w m n).smul_mem _ h₂)
    · by_cases hk : k = 0
      · exact normal_monomial_mem t x y u w m n i j k l r hi (by omega) (Or.inl hk) hdeg
      by_cases hl : l = 0
      · exact normal_monomial_mem t x y u w m n i j k l r hi (by omega) (Or.inr hl) hdeg
      obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
      obtain ⟨c, rfl⟩ : ∃ c, l = c + 1 := ⟨l - 1, by omega⟩
      have h₀ := hsmaller j b c (r + 1) (by omega) (by omega)
      have h₁ := hsmaller (j + 2) b c r (by omega) (by omega)
      have heq : t ^ i * x ^ j * y ^ (b + 1) * u ^ (c + 1) * w ^ r =
          t ^ i * x ^ j * y ^ b * u ^ c * w ^ (r + 1) -
          (2 : ℂ) • (t ^ i * x ^ (j + 2) * y ^ b * u ^ c * w ^ r) := by
        calc
          _ = t ^ i * x ^ j * y ^ b * u ^ c * w ^ r * (y * u) := by ring
          _ = _ := by rw [hw]; simp only [Algebra.smul_def, map_ofNat]; ring
      rw [heq]
      exact (sectionSpan t x y u w m n).sub_mem h₀
        ((sectionSpan t x y u w m n).smul_mem 2 h₁)

private lemma normalized_polynomial_mem (g₂ g₃ : ℂ) (t x y u w : A)
    (hx : x ^ 3 = (1 / 4 : ℂ) • y ^ 2 + (g₂ / 4) • x + (g₃ / 4) • (1 : A))
    (hw : y * u = w - 2 * x ^ 2)
    (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, w] Q ∈ sectionSpan t x y u w m n := by
  rw [Q.as_sum, map_sum]
  apply (sectionSpan t x y u w m n).sum_mem
  intro d hd
  have hh := hQ d hd
  have hmem := all_monomial_mem g₂ g₃ t x y u w hx hw m n (d 1) (d 3) (d 4)
    (d 5) (d 6) (by omega) (by omega)
  have hm := (sectionSpan t x y u w m n).smul_mem (coeff d Q) hmem
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.prod_empty, one_pow, one_mul, mul_one]
  change algebraMap ℂ A (coeff d Q) *
    (t ^ d 1 * (x ^ d 3 * (y ^ d 4 * (u ^ d 5 * w ^ d 6)))) ∈ _
  convert hm using 1
  simp only [Algebra.smul_def]
  ring

private lemma quotient_cubic_relation (L : PeriodPair) :
    firstCubicQuotient L (X 1) ^ 3 =
      (1 / 4 : ℂ) • firstCubicQuotient L (X 2) ^ 2 +
      (L.g₂ / 4) • firstCubicQuotient L (X 1) +
      (L.g₃ / 4) • (1 : FirstCubicCoordinateRing L) := by
  have hzero : firstCubicQuotient L (extensionChartCubic L.g₂ L.g₃ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hpoly : (X (1 : Fin 4) ^ 3 -
      (C (1 / 4 : ℂ) * X 2 ^ 2 + C (L.g₂ / 4) * X 1 + C (L.g₃ / 4))) =
      C (-1 / 4 : ℂ) * extensionChartCubic L.g₂ L.g₃ 0 := by
    simp only [extensionChartCubic, ↓reduceIte]
    simp only [div_eq_mul_inv, map_mul, map_neg, map_one, one_mul]
    have hc : C (4⁻¹ : ℂ) * C 4 = (1 : MvPolynomial (Fin 4) ℂ) := by
      rw [← map_mul]
      norm_num
    linear_combination -(X (1 : Fin 4) ^ 3) * hc
  have heq := congrArg (firstCubicQuotient L) hpoly
  have hC (a : ℂ) : firstCubicQuotient L (C a) =
      algebraMap ℂ (FirstCubicCoordinateRing L) a := (firstCubicQuotient L).commutes a
  simp only [map_sub, map_add, map_mul, map_pow, hC, hzero, mul_zero] at heq
  simp only [Algebra.smul_def (R := ℂ) (A := FirstCubicCoordinateRing L), mul_one]
  exact sub_eq_zero.mp heq

private lemma section_space_le (L : PeriodPair) (m n : ℕ) :
    firstChartSectionSpace L m n ≤ sectionSpan
      (firstCubicQuotient L (X 0)) (firstCubicQuotient L (X 1))
      (firstCubicQuotient L (X 2)) (firstCubicQuotient L (X 3))
      (firstCubicQuotient L (X 2) * firstCubicQuotient L (X 3) +
        2 * firstCubicQuotient L (X 1) ^ 2) m n := by
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
  exact normalized_polynomial_mem L.g₂ L.g₃ _ _ _ _ _
    (quotient_cubic_relation L) (by ring) m n Q hQ

private lemma index_card (m n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (SectionIndex m n) = (m + 1) * (3 * n ^ 2 + 2) := by
  simp only [SectionIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  congr 1
  by_cases h : n = 1
  · subst n
    norm_num [Fin.sum_univ_succ]
  · have hn2 : 2 ≤ n := by omega
    rw [min_eq_left hn2]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, Nat.sub_zero]
    have h1 : n - 1 + 1 = n := by omega
    have h2 : n - 2 + 1 = n - 1 := by omega
    rw [h1, h2]
    have he : n = (n - 1) + 1 := by omega
    nlinarith


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) (m n : ℕ)
    (hn : 1 ≤ n) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ (m + 1) * (3 * n ^ 2 + 2) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ 5 * (m + 1) * n ^ 2 := by
  let t := firstCubicQuotient L (X 0)
  let x := firstCubicQuotient L (X 1)
  let y := firstCubicQuotient L (X 2)
  let u := firstCubicQuotient L (X 3)
  let w := y * u + 2 * x ^ 2
  let V := sectionSpan t x y u w m n
  have hle : firstChartSectionSpace L m n ≤ V := section_space_le L m n
  let : Module.Finite ℂ V := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  let : Module.Finite ℂ (firstChartSectionSpace L m n) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hdimV : Module.finrank ℂ V ≤ Fintype.card (SectionIndex m n) :=
    finrank_range_le_card (R := ℂ) (sectionFamily t x y u w m n)
  have hdim := (Submodule.finrank_mono hle).trans hdimV
  rw [index_card m n hn] at hdim
  refine ⟨inferInstance, hdim, hdim.trans ?_⟩
  calc
    _ ≤ (m + 1) * (5 * n ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by ring
