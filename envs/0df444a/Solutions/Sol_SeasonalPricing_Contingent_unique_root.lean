-- Prove2me | solution 1 for SeasonalPricing.Contingent.unique_root
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:07:03.836244+00:00
-- url     : https://prove2.me/submissions/a2821fde-198b-46e3-8109-f30432f6858c

import Mathlib
import Definitions.Def_SeasonalPricing_Contingent_IsInventoryBelief
import Definitions.Def_SeasonalPricing_Contingent_waitingSurplus

set_option autoImplicit false

open SeasonalPricing.Contingent in
lemma ws4bc7_lip (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (α T t x y : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) (hxy : x ≤ y) :
    waitingSurplus Q pmf alloc p2 α T t y - waitingSurplus Q pmf alloc p2 α T t x ≤
      (Real.exp (-(α * (T - t))) * ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q) * (y - x) := by
  obtain ⟨hp, -, ha, -⟩ := hbelief
  unfold waitingSurplus
  have c0 : 0 ≤ Real.exp (-(α * (T - t))) := (Real.exp_pos _).le
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  have hw : 0 ≤ pmf q * alloc q := mul_nonneg (hp q hq) (ha q hq).1
  have key : max (y * Real.exp (-(α * (T - t))) - p2 q) 0 ≤
      max (x * Real.exp (-(α * (T - t))) - p2 q) 0 + Real.exp (-(α * (T - t))) * (y - x) := by
    apply max_le
    · have := le_max_left (x * Real.exp (-(α * (T - t))) - p2 q) 0
      nlinarith
    · have := le_max_right (x * Real.exp (-(α * (T - t))) - p2 q) 0
      have : 0 ≤ Real.exp (-(α * (T - t))) * (y - x) := mul_nonneg c0 (by linarith)
      linarith
  have := mul_le_mul_of_nonneg_left key hw
  nlinarith

open SeasonalPricing.Contingent in
lemma ws4bc7_nonneg (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (α T t x : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) :
    0 ≤ waitingSurplus Q pmf alloc p2 α T t x := by
  obtain ⟨hp, -, ha, -⟩ := hbelief
  unfold waitingSurplus
  exact Finset.sum_nonneg fun q hq =>
    mul_nonneg (mul_nonneg (hp q hq) (ha q hq).1) (le_max_right _ _)

open SeasonalPricing.Contingent in
lemma ws4bc7_cont (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (α T t : ℝ) :
    Continuous fun x => waitingSurplus Q pmf alloc p2 α T t x := by
  unfold waitingSurplus
  fun_prop

open SeasonalPricing.Contingent in
theorem solution (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (p1 α T t : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hslope : 0 < α ∨ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q < 1) :
    ∃! ψ : ℝ, p1 ≤ ψ ∧ ψ - p1 = waitingSurplus Q pmf alloc p2 α T t ψ := by
  have hL := fun x y (h : x ≤ y) => ws4bc7_lip Q pmf alloc p2 α T t x y hbelief h
  have hN := fun x => ws4bc7_nonneg Q pmf alloc p2 α T t x hbelief
  have hC := ws4bc7_cont Q pmf alloc p2 α T t
  obtain ⟨hp, hsum, ha, -⟩ := hbelief
  set W := ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q with hW
  set c := Real.exp (-(α * (T - t))) with hc
  set S := fun x => waitingSurplus Q pmf alloc p2 α T t x with hS
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun q hq => mul_nonneg (hp q hq) (ha q hq).1
  have hW1 : W ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum fun q hq => by nlinarith [hp q hq, (ha q hq).2]
  have hk : c * W < 1 := by
    rcases hslope with h | h
    · have : c < 1 := by
        rw [hc, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
      nlinarith
    · nlinarith
  have hk' : 0 < 1 - c * W := by linarith
  -- existence via IVT
  set M := p1 + S p1 / (1 - c * W) with hM
  have hSp : 0 ≤ S p1 := hN p1
  have hpM : p1 ≤ M := by
    have : 0 ≤ S p1 / (1 - c * W) := div_nonneg hSp hk'.le
    linarith
  have hfM : 0 ≤ M - p1 - S M := by
    have h1 := hL p1 M hpM
    have h2 : (1 - c * W) * (M - p1) = S p1 := by
      rw [hM]; field_simp; ring
    change S M - S p1 ≤ c * W * (M - p1) at h1
    nlinarith
  have hcont : ContinuousOn (fun x => x - p1 - S x) (Set.Icc p1 M) :=
    (by fun_prop : Continuous fun x => x - p1 - S x).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun x => x - p1 - S x) p1) ((fun x => x - p1 - S x) M) := by
    simp only [Set.mem_Icc]
    constructor
    · linarith
    · exact hfM
  obtain ⟨ψ, ⟨hψ1, -⟩, hψ⟩ := intermediate_value_Icc hpM hcont hmem
  simp only at hψ
  refine ⟨ψ, ⟨hψ1, by change ψ - p1 = S ψ; linarith⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  change y - p1 = S y at hy2
  rcases lt_trichotomy y ψ with h | h | h
  · have := hL y ψ h.le
    change S ψ - S y ≤ c * W * (ψ - y) at this
    nlinarith
  · exact h
  · have := hL ψ y h.le
    change S y - S ψ ≤ c * W * (y - ψ) at this
    nlinarith
