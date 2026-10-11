-- Prove2me | solution 1 for PriceQualityService.Uniform.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:20:27.362579+00:00
-- url     : https://prove2.me/submissions/a9208ec4-ea47-42fa-9f6e-f54329bca02b

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace RRAux_PriceQualityService_Uniform_theorem_3

open PriceQualityService.Joint

theorem term_le (y u : ℝ) : y * Real.exp u ≤ Real.exp (u + y - 1) := by
  rw [show u + y - 1 = (y - 1) + u by ring, Real.exp_add]
  have := Real.add_one_le_exp (y - 1)
  have hu := Real.exp_pos u
  nlinarith

theorem one_add_sum_pos {N : ℕ} (α s p q t : Fin N → ℝ) :
    0 < 1 + ∑ j, attraction α s p q t j := by
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (Real.exp_pos
    (α j * q j - p j + t j * s j)).le)
  unfold attraction
  linarith

theorem prof_mul {N : ℕ} (α a b c s p q t : Fin N → ℝ) :
    profit α a b c s p q t * (1 + ∑ j, attraction α s p q t j) =
      ∑ i, markup a b c p q t i * attraction α s p q t i := by
  have hpos := one_add_sum_pos α s p q t
  unfold profit choiceProb
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem L_le_K (α a b c s : ℝ) (hc : 0 < c) (q t : ℝ) :
    α * q - c * q ^ 2 - t * (a - b * q) + t * s ≤
      b ^ 2 * t ^ 2 / (4 * c) + (s - a + α * b / (2 * c)) * t + α ^ 2 / (4 * c) := by
  have h : b ^ 2 * t ^ 2 / (4 * c) + (s - a + α * b / (2 * c)) * t + α ^ 2 / (4 * c) -
      (α * q - c * q ^ 2 - t * (a - b * q) + t * s) = (2 * c * q - α - t * b) ^ 2 / (4 * c) := by
    field_simp; ring
  have : 0 ≤ (2 * c * q - α - t * b) ^ 2 / (4 * c) := by positivity
  linarith

theorem att_le {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (p q t : Fin N → ℝ)
    (r : ℝ) (i : Fin N) :
    (markup a b c p q t i - r) * attraction α s p q t i ≤
      Real.exp (durationExponent α a b c s i (t i) - r - 1) := by
  have h1 := term_le (markup a b c p q t i - r) (α i * q i - p i + t i * s i)
  have h2 := L_le_K (α i) (a i) (b i) (c i) (s i) (hc i) (q i) (t i)
  unfold attraction
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  unfold durationExponent markup
  linarith

theorem profit_le {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (p q t : Fin N → ℝ)
    (r : ℝ) (hr : ∑ i, Real.exp (durationExponent α a b c s i (t i) - r - 1) ≤ r) :
    profit α a b c s p q t ≤ r := by
  have hpos := one_add_sum_pos α s p q t
  have hm := prof_mul α a b c s p q t
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => att_le α a b c s hc p q t r i)
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  refine le_of_mul_le_mul_right ?_ hpos
  rw [hm]; nlinarith

-- the optimiser attaining r when Σ exp(K_i - r - 1) = r
theorem profit_attained {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (t : Fin N → ℝ)
    (r : ℝ) (hr : ∑ i, Real.exp (durationExponent α a b c s i (t i) - r - 1) = r) :
    profit α a b c s
      (fun i => c i * ((α i + t i * b i) / (2 * c i)) ^ 2 +
        t i * (a i - b i * ((α i + t i * b i) / (2 * c i))) + r + 1)
      (fun i => (α i + t i * b i) / (2 * c i)) t = r := by
  set p : Fin N → ℝ := fun i => c i * ((α i + t i * b i) / (2 * c i)) ^ 2 +
        t i * (a i - b i * ((α i + t i * b i) / (2 * c i))) + r + 1 with hp
  set q : Fin N → ℝ := fun i => (α i + t i * b i) / (2 * c i) with hq
  have hpos := one_add_sum_pos α s p q t
  have hm := prof_mul α a b c s p q t
  have hmk : ∀ i, markup a b c p q t i = r + 1 := by
    intro i; simp only [markup, hp]; ring
  have hatt : ∀ i, attraction α s p q t i =
      Real.exp (durationExponent α a b c s i (t i) - r - 1) := by
    intro i; unfold attraction durationExponent; congr 1; simp only [hp, hq]
    have := hc i
    field_simp; ring
  simp only [hmk, hatt, ← Finset.mul_sum, hr] at hm
  have h1 : (0:ℝ) < 1 + r := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      (Real.exp_pos (durationExponent α a b c s i (t i) - r - 1)).le)
    rw [hr] at this; linarith
  have : profit α a b c s p q t * (1 + r) = r * (1 + r) := by rw [hm]; ring
  exact mul_right_cancel₀ h1.ne' this

-- root of R = S e^{-R-1} for S ≥ 0
theorem exists_root (S : ℝ) (hS : 0 ≤ S) : ∃ R : ℝ, S * Real.exp (-R - 1) = R := by
  have hcont : ContinuousOn (fun R : ℝ => R - S * Real.exp (-R - 1)) (Set.Icc 0 S) := by
    fun_prop
  have h0 : (0:ℝ) - S * Real.exp (-0 - 1) ≤ 0 := by
    have := Real.exp_pos (-0 - 1 : ℝ); nlinarith
  have hSv : 0 ≤ S - S * Real.exp (-S - 1) := by
    have : Real.exp (-S - 1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  obtain ⟨R, _, hR⟩ := intermediate_value_Icc hS hcont ⟨h0, hSv⟩
  exact ⟨R, by simp at hR; linarith⟩

theorem convex_S {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    ConvexOn ℝ Set.univ (fun τ => ∑ i, Real.exp (durationExponent α a b c s i τ)) := by
  refine ⟨convex_univ, fun x _ y _ u v hu hv huv => ?_⟩
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hK : durationExponent α a b c s i (u * x + v * y) ≤
      u * durationExponent α a b c s i x + v * durationExponent α a b c s i y := by
    unfold durationExponent
    have hv' : v = 1 - u := by linarith
    subst hv'
    have hci := hc i
    have hk : 0 ≤ b i ^ 2 / (4 * c i) := by positivity
    have e : u * (b i ^ 2 * x ^ 2 / (4 * c i) + (s i - a i + α i * b i / (2 * c i)) * x
        + α i ^ 2 / (4 * c i)) + (1 - u) * (b i ^ 2 * y ^ 2 / (4 * c i) +
        (s i - a i + α i * b i / (2 * c i)) * y + α i ^ 2 / (4 * c i)) -
        (b i ^ 2 * (u * x + (1 - u) * y) ^ 2 / (4 * c i) +
        (s i - a i + α i * b i / (2 * c i)) * (u * x + (1 - u) * y) + α i ^ 2 / (4 * c i))
        = b i ^ 2 / (4 * c i) * (u * (1 - u) * (x - y) ^ 2) := by
      field_simp; ring
    have : 0 ≤ b i ^ 2 / (4 * c i) * (u * (1 - u) * (x - y) ^ 2) := by
      apply mul_nonneg hk; apply mul_nonneg (mul_nonneg hu hv) (sq_nonneg _)
    linarith
  calc Real.exp (durationExponent α a b c s i (u * x + v * y))
      ≤ Real.exp (u * durationExponent α a b c s i x + v * durationExponent α a b c s i y) :=
        Real.exp_le_exp.mpr hK
    _ ≤ u * Real.exp (durationExponent α a b c s i x) +
          v * Real.exp (durationExponent α a b c s i y) := by
        have := convexOn_exp.2 (Set.mem_univ (durationExponent α a b c s i x))
          (Set.mem_univ (durationExponent α a b c s i y)) hu hv huv
        simpa [smul_eq_mul] using this

end RRAux_PriceQualityService_Uniform_theorem_3

open RRAux_PriceQualityService_Uniform_theorem_3 in
-- Theorem 3, Wang, Ke & Cui
theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hts : ts ≤ tl) :
    ∃ τ : ℝ, (τ = ts ∨ τ = tl) ∧ ∃ pStar qStar : Fin N → ℝ,
      ∀ t ∈ Set.Icc ts tl, ∀ p q : Fin N → ℝ,
        PriceQualityService.Joint.profit α a b c s p q (fun _ => t) ≤ PriceQualityService.Joint.profit α a b c s pStar qStar (fun _ => τ) := by
  let S : ℝ → ℝ := fun τ => ∑ i, Real.exp (PriceQualityService.Joint.durationExponent α a b c s i τ)
  have hconv : ConvexOn ℝ Set.univ S := convex_S α a b c s hc
  obtain ⟨τ, hτ, hmax⟩ : ∃ τ : ℝ, (τ = ts ∨ τ = tl) ∧ max (S ts) (S tl) = S τ := by
    rcases le_total (S ts) (S tl) with h | h
    · exact ⟨tl, Or.inr rfl, max_eq_right h⟩
    · exact ⟨ts, Or.inl rfl, max_eq_left h⟩
  have hSnn : 0 ≤ S τ := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  obtain ⟨R, hR⟩ := exists_root (S τ) hSnn
  have hsumR : ∀ τ' : ℝ, ∑ i, Real.exp
      (PriceQualityService.Joint.durationExponent α a b c s i τ' - R - 1) = S τ' * Real.exp (-R - 1) := by
    intro τ'
    simp only [S, Finset.sum_mul, ← Real.exp_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; ring
  refine ⟨τ, hτ, fun i => c i * ((α i + τ * b i) / (2 * c i)) ^ 2 +
        τ * (a i - b i * ((α i + τ * b i) / (2 * c i))) + R + 1,
    fun i => (α i + τ * b i) / (2 * c i), fun t ht p q => ?_⟩
  rw [profit_attained α a b c s hc (fun _ => τ) R (by rw [hsumR τ, hR])]
  apply profit_le α a b c s hc
  rw [hsumR t]
  conv_rhs => rw [← hR]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [← hmax]
  exact hconv.le_max_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) ht

#print axioms solution
