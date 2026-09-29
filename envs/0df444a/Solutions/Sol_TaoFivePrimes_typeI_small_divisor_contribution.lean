-- Prove2me | solution 1 for TaoFivePrimes.typeI_small_divisor_contribution
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:31:49.612141+00:00
-- url     : https://prove2.me/submissions/122f4d58-0ebd-4f42-8707-b92abcf16205

import Mathlib
import Theorems.Thm_TaoFivePrimes_vinogradov_odd

open Finset

section PartS5S
open Finset
namespace TaoS5S

/-- The weight appearing in the Type I estimate, with the source's convention at the
zeros of the sine. -/
noncomputable def wgt (A B alpha : ℝ) (d : ℤ) : ℝ :=
  if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then A
    else min A (B / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)

theorem wgt_nonneg {A B alpha : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (d : ℤ) : 0 ≤ wgt A B alpha d := by
  unfold wgt
  split_ifs with h
  · exact hA
  · exact le_min hA (by positivity)

theorem wgt_neg (A B alpha : ℝ) (d : ℤ) : wgt A B alpha (-d) = wgt A B alpha d := by
  unfold wgt
  have h : Real.pi * (2 * alpha) * ((-d : ℤ) : ℝ)
      = -(Real.pi * (2 * alpha) * ((d : ℤ) : ℝ)) := by push_cast; ring
  simp only [h, Real.sin_neg, abs_neg, neg_eq_zero]

/-- **Tao, Section 5**: the contribution of the divisors `d ≤ q/2` to the Type I envelope.
Symmetrizing the range and applying Corollary 3.5 once gains the factor two. -/
theorem small_divisor_sum
    (A B alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A
              else min A (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) :
    (∑ d ∈ (Finset.Ioc (0 : ℤ) ⌊(q : ℝ) / 2⌋).filter (fun d : ℤ => Odd d),
        wgt A B alpha d)
      ≤ A + (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set u : ℝ := -((q : ℝ) / 2) - 1 with hu
  set v : ℝ := (q : ℝ) / 2 with hv
  have huv : u < v := by rw [hu, hv]; linarith
  -- Corollary 3.5 on the symmetric range
  have hcor := TaoFivePrimes.vinogradov_odd A B (2 * alpha) beta 0 a q (by omega)
    (by rw [← halpha]; ring) hbeta u v huv hvino
  -- the factor in front is `1`
  have hfloor : (⌊(v - u) / (2 * (q : ℝ))⌋ : ℤ) = 0 := by
    have h1 : v - u = (q : ℝ) + 1 := by rw [hu, hv]; ring
    rw [h1]
    have h2 : (0 : ℝ) ≤ ((q : ℝ) + 1) / (2 * (q : ℝ)) := by positivity
    have h3 : ((q : ℝ) + 1) / (2 * (q : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    exact Int.floor_eq_zero_iff.mpr ⟨h2, h3⟩
  rw [hfloor] at hcor
  simp only [Int.cast_zero, zero_add, one_mul, add_zero] at hcor
  -- the symmetric sum dominates twice the positive part
  set P : Finset ℤ := (Finset.Ioc (0 : ℤ) ⌊(q : ℝ) / 2⌋).filter (fun d : ℤ => Odd d) with hP
  set S : Finset ℤ := (Finset.Ioc ⌊u⌋ ⌊v⌋).filter (fun d : ℤ => Odd d) with hS
  have hfl : ⌊v⌋ = ⌊(q : ℝ) / 2⌋ := by rw [hv]
  have hneg : P.image (fun d : ℤ => -d) ⊆ S := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd1, hd2⟩, hdodd⟩ := hd
    have hdle : (d : ℝ) ≤ (q : ℝ) / 2 := by
      have := Int.floor_le ((q : ℝ) / 2)
      have hcast : ((d : ℤ) : ℝ) ≤ ((⌊(q : ℝ) / 2⌋ : ℤ) : ℝ) := by exact_mod_cast hd2
      linarith
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hdodd.neg⟩
    · rw [Int.lt_iff_add_one_le, ← Int.lt_iff_add_one_le]
      rw [Int.floor_lt, hu]
      push_cast
      linarith
    · rw [hfl]
      have : (1 : ℤ) ≤ d := hd1
      omega
  have hdisj : Disjoint P (P.image (fun d : ℤ => -d)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨d, hd, hdz⟩ := Finset.mem_image.mp hz'
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hz hd
    omega
  have hPS : P ⊆ S := by
    intro d hd
    rw [hP, Finset.mem_filter, Finset.mem_Ioc] at hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hd.2⟩
    · have h0 : ⌊u⌋ < 0 := by
        rw [Int.floor_lt, hu]
        push_cast
        linarith
      omega
    · rw [hfl]; exact hd.1.2
  have hsub : P ∪ P.image (fun d : ℤ => -d) ⊆ S := Finset.union_subset hPS hneg
  have hsplit : (∑ d ∈ P ∪ P.image (fun d : ℤ => -d), wgt A B alpha d)
      = (∑ d ∈ P, wgt A B alpha d) + ∑ d ∈ P.image (fun d : ℤ => -d), wgt A B alpha d :=
    Finset.sum_union hdisj
  have himg : (∑ d ∈ P.image (fun d : ℤ => -d), wgt A B alpha d) = ∑ d ∈ P, wgt A B alpha d := by
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    exact Finset.sum_congr rfl (fun d _ => wgt_neg A B alpha d)
  have hle : (∑ d ∈ P ∪ P.image (fun d : ℤ => -d), wgt A B alpha d) ≤ ∑ d ∈ S, wgt A B alpha d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => wgt_nonneg hA hB d)
  have hcor' : (∑ d ∈ S, wgt A B alpha d)
      ≤ 2 * A + 2 / Real.pi * B * (q : ℝ) * Real.log (4 * q) := by
    rw [hS]
    exact hcor
  have hkey : 2 * (∑ d ∈ P, wgt A B alpha d)
      ≤ 2 * A + 2 / Real.pi * B * (q : ℝ) * Real.log (4 * q) := by
    rw [hsplit, himg] at hle
    linarith [hle, hcor']
  have hpi : (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)
      = (2 / Real.pi * B * (q : ℝ) * Real.log (4 * q)) / 2 := by ring
  linarith [hkey, hpi]

end TaoS5S
end PartS5S

theorem solution
    (A B alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 2 ≤ q)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A
              else min A (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) :
    (∑ d ∈ (Finset.Ioc (0 : ℤ) ⌊(q : ℝ) / 2⌋).filter (fun d : ℤ => Odd d),
        (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then A
          else min A (B / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|)))
      ≤ A + (1 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) :=
  TaoS5S.small_divisor_sum A B alpha beta a q hq hA hB halpha hbeta hvino
