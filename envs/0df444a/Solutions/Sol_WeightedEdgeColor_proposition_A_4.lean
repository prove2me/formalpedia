-- Prove2me | solution 1 for WeightedEdgeColor.proposition_A_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:47:51.982797+00:00
-- url     : https://prove2.me/submissions/ad505842-c62f-4de4-abcb-eda58aaaed16

import Mathlib
import Theorems.Thm_PartialResampling_pra_sums

set_option autoImplicit false
open Finset

namespace WECA4proof

/-- termwise: μ * exp(m/(μ+m)) ≤ μ + m -/
theorem term_le (μ m : ℝ) (hμ : 0 ≤ μ) (hm : 0 < m) : μ * Real.exp (m / (μ + m)) ≤ μ + m := by
  rcases hμ.eq_or_lt with h | h
  · rw [← h]; simp; linarith
  · have hx : m / (μ + m) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h1 := Real.add_one_le_exp (-(m / (μ + m)))
    have h2 : Real.exp (m / (μ + m)) * Real.exp (-(m / (μ + m))) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 1 - m / (μ + m) = μ / (μ + m) := by field_simp; ring
    have he := Real.exp_pos (m / (μ + m))
    have : Real.exp (m / (μ + m)) * (μ / (μ + m)) ≤ 1 := by
      rw [← h3, ← h2]; apply mul_le_mul_of_nonneg_left _ he.le; linarith
    rw [mul_div_assoc', div_le_one (by linarith)] at this
    linarith

theorem prod_lower (μ : ℝ) (hμ : 0 ≤ μ) : ∀ n : ℕ,
    μ ^ n * Real.exp (∑ j ∈ range n, ((j : ℝ) + 1) / (μ + j + 1)) ≤ ∏ j ∈ range n, (μ + 1 + j)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, Real.exp_add, Finset.prod_range_succ, pow_succ]
    have IH := prod_lower μ hμ n
    have ht := term_le μ ((n : ℝ) + 1) hμ (by positivity)
    have e : μ + ((n : ℝ) + 1) = μ + n + 1 := by ring
    rw [e] at ht
    have hpos1 : 0 ≤ μ ^ n * Real.exp (∑ j ∈ range n, ((j : ℝ) + 1) / (μ + j + 1)) := by positivity
    calc μ ^ n * μ * (Real.exp (∑ j ∈ range n, ((j : ℝ) + 1) / (μ + j + 1)) *
          Real.exp (((n : ℝ) + 1) / (μ + n + 1)))
        = (μ ^ n * Real.exp (∑ j ∈ range n, ((j : ℝ) + 1) / (μ + j + 1))) *
          (μ * Real.exp (((n : ℝ) + 1) / (μ + n + 1))) := by ring
      _ ≤ (∏ j ∈ range n, (μ + 1 + j)) * (μ + 1 + n) := by
          apply mul_le_mul IH (by linarith) (by positivity)
          exact le_trans hpos1 IH
    
theorem gauss : ∀ n : ℕ, ∑ j ∈ range n, ((j : ℝ) + 1) = (n : ℝ) * (n + 1) / 2
  | 0 => by simp
  | k + 1 => by rw [Finset.sum_range_succ, gauss k]; push_cast; ring

theorem sum_ge (μ : ℝ) (hμ : 0 ≤ μ) (n : ℕ) :
    ((n : ℝ) * (n + 1)) / (2 * (μ + n + 1)) ≤ ∑ j ∈ range n, ((j : ℝ) + 1) / (μ + j + 1) := by
  have h1 : ∀ j ∈ range n, ((j : ℝ) + 1) / (μ + n + 1) ≤ ((j : ℝ) + 1) / (μ + j + 1) := by
    intro j hj
    have := Finset.mem_range.mp hj
    have hj' : (j : ℝ) ≤ n := by exact_mod_cast this.le
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  refine le_trans ?_ (Finset.sum_le_sum h1)
  rw [← Finset.sum_div]
  rw [gauss n]
  rw [div_div, mul_comm 2 (μ + n + 1)]

/-- main analytic bound: (μ+d) μ^(d-1) ≤ ff * exp(-(d-1)d/(2(μ+d))) -/
theorem ff_bound (μ τ : ℝ) (d : ℕ) (hμ : 0 ≤ μ) (hd : 1 ≤ d) (hτ : μ + d ≤ τ) :
    (μ + d) * μ ^ (d - 1) ≤ (∏ j ∈ range d, (τ - j)) *
      Real.exp (-(((d : ℝ) - 1) * d / (2 * (μ + d)))) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hrefl : ∏ j ∈ range (n + 1), (μ + (n + 1 : ℕ) - j) = ∏ j ∈ range (n + 1), (μ + 1 + j) := by
    rw [← Finset.prod_range_reflect (fun j => μ + 1 + j) (n + 1)]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have := Finset.mem_range.mp hj
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hmono : ∏ j ∈ range (n + 1), (μ + (n + 1 : ℕ) - j) ≤ ∏ j ∈ range (n + 1), (τ - j) := by
    refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => by linarith)
    have := Finset.mem_range.mp hj
    have : (j : ℝ) + 1 ≤ (n + 1 : ℕ) := by exact_mod_cast this
    linarith
  have hP := prod_lower μ hμ n
  have hsg := sum_ge μ hμ n
  rw [hrefl] at hmono
  have hsplit : ∏ j ∈ range (n + 1), (μ + 1 + j) = (∏ j ∈ range n, (μ + 1 + j)) * (μ + 1 + n) :=
    Finset.prod_range_succ _ _
  have hE : Real.exp (((n : ℝ)) * (n + 1) / (2 * (μ + n + 1))) ≤
      Real.exp (∑ j ∈ range n, ((j : ℝ) + 1) / (μ + j + 1)) := Real.exp_le_exp.mpr hsg
  have hexpos := Real.exp_pos (-((((n + 1 : ℕ) : ℝ) - 1) * ((n + 1 : ℕ) : ℝ) / (2 * (μ + ((n + 1 : ℕ) : ℝ)))))
  have hkey : Real.exp (-((((n + 1 : ℕ) : ℝ) - 1) * ((n + 1 : ℕ) : ℝ) / (2 * (μ + ((n + 1 : ℕ) : ℝ))))) *
      Real.exp (((n : ℝ)) * (n + 1) / (2 * (μ + n + 1))) = 1 := by
    rw [← Real.exp_add]; push_cast; ring_nf; simp
  push_cast at hexpos hkey ⊢
  have hmu_pow : 0 ≤ μ ^ n := pow_nonneg hμ n
  calc (μ + (n + 1)) * μ ^ n
      = (μ + (n + 1)) * μ ^ n * (Real.exp (-((n + 1 - 1) * (n + 1) / (2 * (μ + (n + 1))))) *
          Real.exp ((n : ℝ) * (n + 1) / (2 * (μ + n + 1)))) := by rw [hkey, mul_one]
    _ ≤ (μ + (n + 1)) * (μ ^ n * Real.exp (∑ j ∈ range n, ((j : ℝ) + 1) / (μ + j + 1))) *
          Real.exp (-((n + 1 - 1) * (n + 1) / (2 * (μ + (n + 1))))) := by
        have := mul_le_mul_of_nonneg_left hE hmu_pow
        have h2 : 0 ≤ (μ + (n + 1)) * Real.exp (-((n + 1 - 1) * (n + 1) / (2 * (μ + (n + 1))))) := by
          positivity
        nlinarith
    _ ≤ (μ + (n + 1)) * (∏ j ∈ range n, (μ + 1 + j)) *
          Real.exp (-((n + 1 - 1) * (n + 1) / (2 * (μ + (n + 1))))) := by
        apply mul_le_mul_of_nonneg_right _ hexpos.le
        exact mul_le_mul_of_nonneg_left hP (by linarith)
    _ ≤ (∏ j ∈ range (n + 1), (τ - j)) * Real.exp (-((n + 1 - 1) * (n + 1) / (2 * (μ + (n + 1))))) := by
        apply mul_le_mul_of_nonneg_right _ hexpos.le
        rw [hsplit] at hmono
        linarith [hmono]

end WECA4proof

open WECA4proof in
theorem solution :
    ∃ K : ℝ, ∀ (I T : Type) [Fintype I] [Fintype T] (Ω : I → Type) [∀ i, Fintype (Ω i)]
      (p : ∀ i, Ω i → ℝ) (f : T → ∀ i, Ω i → ℝ) (R D : ℝ),
      (∀ i ω, 0 < p i ω) → (∀ i, ∑ ω, p i ω = 1) →
      (∀ t i ω, 0 ≤ f t i ω ∧ f t i ω ≤ 1) →
      (∀ t, ∑ i, ∑ ω, p i ω * f t i ω ≤ R) →
      (∀ i ω, ∑ t, f t i ω ≤ D) →
      ∃ z : ∀ i, Ω i, ∀ t, ∑ i, f t i (z i) ≤ ∑ i, ∑ ω, p i ω * f t i ω +
        K * (Real.sqrt (R * Real.log (max 2 (max R D) + 2)) + Real.log (max 2 (max R D) + 2)) := by
  refine ⟨100, ?_⟩
  intro I T _ _ Ω _ p f R D hp hp1 hf hR hD
  classical
  set C := max 2 (max R D) with hC
  set L := Real.log (C + 2) with hL
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCR : R ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCD : D ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  set m : T → ℝ := fun t => ∑ i, ∑ ω, p i ω * f t i ω with hm
  have hm0 : ∀ t, 0 ≤ m t := fun t => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun ω _ => mul_nonneg (hp i ω).le (hf t i ω).1))
  set s := Real.sqrt (R * L) with hs
  set A := 100 * (s + L) with hA
  set ε := 1 / C with hε
  set Λ := 1 + ε with hΛ
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 / 2 := by rw [hε]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hεm : ∀ t, ε * m t ≤ 1 := by
    intro t
    have h1 : m t ≤ C := le_trans (hR t) hCR
    rw [hε, one_div_mul_eq_div, div_le_one (by linarith)]; exact h1
  set τ : T → ℝ := fun t => m t + A with hτ
  set μ : T → ℝ := fun t => Λ * m t with hμ
  have hμτ : ∀ t, μ t ≤ m t + 1 := fun t => by simp only [hμ, hΛ]; linarith [hεm t]
  set d : T → ℕ := fun t => ⌊τ t - μ t⌋₊ with hd
  have hsL : 0 ≤ s := Real.sqrt_nonneg _
  have hA100 : 100 ≤ A := by rw [hA]; nlinarith
  have hdτ : ∀ t, (d t : ℝ) ≤ τ t - μ t := fun t => Nat.floor_le (by
    simp only [hτ, hμ, hΛ]; nlinarith [hεm t])
  have hdlow : ∀ t, A - 2 ≤ (d t : ℝ) := by
    intro t
    have := Nat.lt_floor_add_one (τ t - μ t)
    simp only [hd] at this ⊢
    simp only [hτ, hμ, hΛ] at this
    nlinarith [hεm t]
  have hd1 : ∀ t, 1 ≤ d t := fun t => by
    have := hdlow t
    have : (1 : ℝ) ≤ d t := by linarith
    exact_mod_cast this
  have hμ0 : ∀ t, 0 ≤ μ t := fun t => mul_nonneg (by linarith) (hm0 t)
  -- the exponent bound
  have hX : ∀ t, 4 * L ≤ ((d t : ℝ) - 1) * d t / (2 * (μ t + d t)) := by
    intro t
    have hR0 : 0 ≤ R := le_trans (hm0 t) (hR t)
    have hs2 : s ^ 2 = R * L := Real.sq_sqrt (by positivity)
    have hdl := hdlow t
    have hμd : μ t + d t ≤ R + A := by
      have := hdτ t
      have : m t ≤ R := hR t
      simp only [hτ] at *
      linarith
    have hpos : 0 < μ t + d t := by have := hμ0 t; have : (1 : ℝ) ≤ d t := by exact_mod_cast hd1 t
                                    linarith
    rw [le_div_iff₀ (by linarith)]
    have h1 : (A - 3) * (A - 2) ≤ ((d t : ℝ) - 1) * d t := by
      apply mul_le_mul (by linarith) hdl (by linarith) (by linarith)
    have h2 : 8 * L * (R + A) ≤ (A - 3) * (A - 2) := by
      rw [hA]
      nlinarith [hs2, hsL, hL1, mul_nonneg hsL (by linarith : (0:ℝ) ≤ L)]
    nlinarith
  have hE : ∀ t, Real.exp (-(((d t : ℝ) - 1) * d t / (2 * (μ t + d t)))) ≤ 1 / (C + 2) ^ 4 := by
    intro t
    have : Real.exp (-(4 * L)) = 1 / (C + 2) ^ 4 := by
      rw [Real.exp_neg, hL, show 4 * Real.log (C + 2) = Real.log ((C + 2) ^ 4) by
        rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div]
    rw [← this]
    exact Real.exp_le_exp.mpr (by linarith [hX t])
  have hC4 : 8 * C ^ 2 ≤ (C + 2) ^ 4 := by nlinarith [sq_nonneg C, sq_nonneg (C + 2)]
  have hff : ∀ t, (μ t + d t) * μ t ^ (d t - 1) ≤
      (∏ j ∈ range (d t), (τ t - j)) / (C + 2) ^ 4 := by
    intro t
    have := ff_bound (μ t) (τ t) (d t) (hμ0 t) (hd1 t) (by linarith [hdτ t])
    have hP : 0 ≤ ∏ j ∈ range (d t), (τ t - j) := by
      refine Finset.prod_nonneg (fun j hj => ?_)
      have := Finset.mem_range.mp hj
      have : (j : ℝ) + 1 ≤ d t := by exact_mod_cast this
      linarith [hdτ t, hμ0 t]
    calc _ ≤ _ := this
      _ ≤ (∏ j ∈ range (d t), (τ t - j)) * (1 / (C + 2) ^ 4) := mul_le_mul_of_nonneg_left (hE t) hP
      _ = _ := by ring
  have hSg : ∀ t, (Λ * ∑ i, ∑ ω, p i ω * f t i ω) ^ d t ≤
      (∏ j ∈ Finset.range (d t), (τ t - j)) / 4 := by
    intro t
    have h1 := hff t
    have hP4 : (∏ j ∈ range (d t), (τ t - j)) / (C + 2) ^ 4 ≤ (∏ j ∈ range (d t), (τ t - j)) / 4 := by
      have hP : 0 ≤ ∏ j ∈ range (d t), (τ t - j) := by
        refine Finset.prod_nonneg (fun j hj => ?_)
        have := Finset.mem_range.mp hj
        have : (j : ℝ) + 1 ≤ d t := by exact_mod_cast this
        linarith [hdτ t, hμ0 t]
      apply div_le_div_of_nonneg_left hP (by norm_num) (by nlinarith)
    have h2 : μ t ^ d t ≤ (μ t + d t) * μ t ^ (d t - 1) := by
      obtain ⟨n, hn⟩ : ∃ n, d t = n + 1 := ⟨d t - 1, by have := hd1 t; omega⟩
      rw [hn, Nat.add_sub_cancel, pow_succ]
      have := pow_nonneg (hμ0 t) n
      nlinarith [hμ0 t]
    show μ t ^ d t ≤ _
    linarith
  have hGg : ∀ i, ∑ t, (d t : ℝ) * (Λ * ∑ ω, p i ω * f t i ω) *
        (Λ * ∑ u, ∑ ω, p u ω * f t u ω) ^ (d t - 1) / ∏ j ∈ Finset.range (d t), (τ t - j) ≤
      Real.log Λ / 2 := by
    intro i
    have hlog : ε / 2 ≤ Real.log Λ := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < Λ by rw [hΛ]; linarith)
      have h2 : ε / 2 ≤ 1 - Λ⁻¹ := by
        rw [hΛ, show (1 : ℝ) - (1 + ε)⁻¹ = ε / (1 + ε) by field_simp; ring]
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
      linarith
    have hterm : ∀ t, (d t : ℝ) * (Λ * ∑ ω, p i ω * f t i ω) *
        (Λ * ∑ u, ∑ ω, p u ω * f t u ω) ^ (d t - 1) / ∏ j ∈ range (d t), (τ t - j) ≤
        (Λ * ∑ ω, p i ω * f t i ω) / (C + 2) ^ 4 := by
      intro t
      have h1 := hff t
      have hpos : 0 < ∏ j ∈ range (d t), (τ t - j) := by
        refine Finset.prod_pos (fun j hj => ?_)
        have := Finset.mem_range.mp hj
        have : (j : ℝ) + 1 ≤ d t := by exact_mod_cast this
        linarith [hdτ t, hμ0 t]
      have hmi : 0 ≤ Λ * ∑ ω, p i ω * f t i ω := mul_nonneg (by linarith)
        (Finset.sum_nonneg (fun ω _ => mul_nonneg (hp i ω).le (hf t i ω).1))
      have hμeq : Λ * ∑ u, ∑ ω, p u ω * f t u ω = μ t := rfl
      rw [hμeq, div_le_div_iff₀ hpos (by positivity)]
      have h3 : (d t : ℝ) * μ t ^ (d t - 1) ≤ (μ t + d t) * μ t ^ (d t - 1) :=
        mul_le_mul_of_nonneg_right (by linarith [hμ0 t]) (pow_nonneg (hμ0 t) _)
      rw [le_div_iff₀ (by positivity)] at h1
      have h4 : (d t : ℝ) * μ t ^ (d t - 1) * (C + 2) ^ 4 ≤ ∏ j ∈ range (d t), (τ t - j) := by
        have := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ (C + 2) ^ 4)
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h4 hmi]
    refine le_trans (Finset.sum_le_sum (fun t _ => hterm t)) ?_
    rw [← Finset.sum_div]
    have hsum : ∑ t, Λ * ∑ ω, p i ω * f t i ω ≤ Λ * C := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [Finset.sum_comm]
      calc ∑ ω, ∑ t, p i ω * f t i ω = ∑ ω, p i ω * ∑ t, f t i ω := by
            simp_rw [Finset.mul_sum]
        _ ≤ ∑ ω, p i ω * C := Finset.sum_le_sum (fun ω _ =>
            mul_le_mul_of_nonneg_left (le_trans (hD i ω) hCD) (hp i ω).le)
        _ = C := by rw [← Finset.sum_mul, hp1 i, one_mul]
    have hΛ32 : Λ ≤ 3 / 2 := by rw [hΛ]; linarith
    have hC0 : 0 < C := by linarith
    have hCC : (C + 2) ^ 4 > 0 := by positivity
    rw [div_le_iff₀ hCC]
    have hεC : ε * C = 1 := by rw [hε]; field_simp
    nlinarith [hlog, hC4, hsum, mul_le_mul_of_nonneg_right hΛ32 hC0.le]
  obtain ⟨z, hz⟩ := PartialResampling.pra_sums Ω p hp hp1 f hf τ d (fun t => ⟨hd1 t, by
      linarith [hdτ t, hμ0 t]⟩) Λ (by linarith) hSg hGg
  refine ⟨z, fun t => ?_⟩
  have := hz t
  simp only [hτ, hm] at this
  linarith
