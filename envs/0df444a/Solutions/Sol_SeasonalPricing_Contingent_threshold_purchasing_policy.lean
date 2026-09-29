-- Prove2me | solution 1 for SeasonalPricing.Contingent.threshold_purchasing_policy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T05:38:02.387542+00:00
-- url     : https://prove2.me/submissions/a93071d8-cdb2-414b-9d46-ec00e076d69f

import Mathlib
import Definitions.Def_SeasonalPricing_Contingent_IsInventoryBelief
import Definitions.Def_SeasonalPricing_Contingent_waitingSurplus

set_option autoImplicit false

theorem f7a55159_lip (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (c x y : ℝ)
    (hcoef : ∀ q ∈ Finset.range (Q + 1), 0 ≤ pmf q * alloc q) (hc : 0 ≤ c) (hxy : y ≤ x) :
    (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q * max (x * c - p2 q) 0) -
      (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q * max (y * c - p2 q) 0) ≤
      (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q) * (c * (x - y)) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  have h1 := hcoef q hq
  have h2 : max (x * c - p2 q) 0 - max (y * c - p2 q) 0 ≤ c * (x - y) := by
    have hd : 0 ≤ c * (x - y) := mul_nonneg hc (by linarith)
    have : max (x * c - p2 q) 0 ≤ max (y * c - p2 q) 0 + c * (x - y) := by
      apply max_le
      · have := le_max_left (y * c - p2 q) 0
        linarith
      · have := le_max_right (y * c - p2 q) 0
        linarith
    linarith
  calc pmf q * alloc q * max (x * c - p2 q) 0 - pmf q * alloc q * max (y * c - p2 q) 0
      = pmf q * alloc q * (max (x * c - p2 q) 0 - max (y * c - p2 q) 0) := by ring
    _ ≤ pmf q * alloc q * (c * (x - y)) := mul_le_mul_of_nonneg_left h2 h1

theorem f7a55159_monoc (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (c1 c2 x : ℝ)
    (hcoef : ∀ q ∈ Finset.range (Q + 1), 0 ≤ pmf q * alloc q) (hx : 0 ≤ x) (hc : c1 ≤ c2) :
    (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q * max (x * c1 - p2 q) 0) ≤
      (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q * max (x * c2 - p2 q) 0) := by
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left _ (hcoef q hq)
  have : x * c1 ≤ x * c2 := mul_le_mul_of_nonneg_left hc hx
  exact max_le_max (by linarith) (le_refl 0)

theorem f7a55159_nonneg (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (c x : ℝ)
    (hcoef : ∀ q ∈ Finset.range (Q + 1), 0 ≤ pmf q * alloc q) :
    0 ≤ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q * max (x * c - p2 q) 0 :=
  Finset.sum_nonneg (fun q hq => mul_nonneg (hcoef q hq) (le_max_right _ _))

theorem f7a55159_cont (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (c : ℝ) :
    Continuous (fun x : ℝ =>
      ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q * max (x * c - p2 q) 0) := by
  apply continuous_finsetSum
  intro q _
  exact continuous_const.mul
    (((continuous_id.mul continuous_const).sub continuous_const).max continuous_const)

theorem f7a55159_strict (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (p1 c : ℝ)
    (hcoef : ∀ q ∈ Finset.range (Q + 1), 0 ≤ pmf q * alloc q) (hc : 0 ≤ c)
    (hk : c * (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q) < 1) :
    StrictMono (fun x : ℝ =>
      x - p1 - ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q * max (x * c - p2 q) 0) := by
  intro y x hxy
  have hl := f7a55159_lip Q pmf alloc p2 c x y hcoef hc hxy.le
  have hpos : 0 < x - y := by linarith
  have h3 := mul_lt_mul_of_pos_right hk hpos
  have e : (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q) * (c * (x - y)) =
      c * (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q) * (x - y) := by ring
  simp only
  linarith

open SeasonalPricing.Contingent in
theorem solution (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (p1 α T : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) (hα : 0 ≤ α) (hT : 0 < T)
    (hp1 : 0 ≤ p1) (hp2 : ∀ q ∈ Finset.Icc 1 Q, p2 q ≤ p1)
    (hslope : 0 < α ∨ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q < 1) :
    (∀ t ∈ Set.Ico 0 T,
      ∃! ψ : ℝ, p1 ≤ ψ ∧ ψ - p1 = waitingSurplus Q pmf alloc p2 α T t ψ) ∧
    (∀ t ∈ Set.Ico 0 T, ∀ ψ : ℝ,
      p1 ≤ ψ → ψ - p1 = waitingSurplus Q pmf alloc p2 α T t ψ →
      ∀ v : ℝ, buysNow Q pmf alloc p2 p1 α T t v ↔ ψ ≤ v) ∧
    (∀ ψ : ℝ → ℝ,
      (∀ t ∈ Set.Ico 0 T,
        p1 ≤ ψ t ∧ ψ t - p1 = waitingSurplus Q pmf alloc p2 α T t (ψ t)) →
      MonotoneOn ψ (Set.Ico 0 T)) := by
  obtain ⟨hpmf, hsum, halloc, _h0⟩ := hbelief
  have hcoef : ∀ q ∈ Finset.range (Q + 1), 0 ≤ pmf q * alloc q :=
    fun q hq => mul_nonneg (hpmf q hq) (halloc q hq).1
  have hS0 : 0 ≤ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q := Finset.sum_nonneg hcoef
  have hS1 : ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q ≤ 1 := by
    calc ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q
        ≤ ∑ q ∈ Finset.range (Q + 1), pmf q := by
          apply Finset.sum_le_sum
          intro q hq
          have := hpmf q hq
          have := (halloc q hq).2
          nlinarith
      _ = 1 := hsum
  have hcpos : ∀ t : ℝ, 0 ≤ Real.exp (-(α * (T - t))) := fun t => (Real.exp_pos _).le
  have hk : ∀ t ∈ Set.Ico 0 T,
      Real.exp (-(α * (T - t))) * (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q) < 1 := by
    intro t ht
    have hTt : 0 < T - t := by linarith [ht.2]
    have hc1 : Real.exp (-(α * (T - t))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hα hTt.le])
    rcases hslope with hα' | hS'
    · have hc2 : Real.exp (-(α * (T - t))) < 1 :=
        by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos hα' hTt])
      nlinarith [Real.exp_pos (-(α * (T - t)))]
    · nlinarith [Real.exp_pos (-(α * (T - t)))]
  have hstrict : ∀ t ∈ Set.Ico 0 T,
      StrictMono (fun x : ℝ => x - p1 - waitingSurplus Q pmf alloc p2 α T t x) :=
    fun t ht => f7a55159_strict Q pmf alloc p2 p1 _ hcoef (hcpos t) (hk t ht)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hf := hstrict t ht
    have hcont : Continuous (fun x : ℝ => x - p1 - waitingSurplus Q pmf alloc p2 α T t x) :=
      (continuous_id.sub continuous_const).sub
        (f7a55159_cont Q pmf alloc p2 (Real.exp (-(α * (T - t)))))
    have hW0 : 0 ≤ waitingSurplus Q pmf alloc p2 α T t p1 :=
      f7a55159_nonneg Q pmf alloc p2 _ p1 hcoef
    have hkt := hk t ht
    have hne : (1 - Real.exp (-(α * (T - t))) *
        (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q)) ≠ 0 := by
      intro h; linarith
    obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = p1 + waitingSurplus Q pmf alloc p2 α T t p1 /
        (1 - Real.exp (-(α * (T - t))) * (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q)) :=
      ⟨_, rfl⟩
    have hM : p1 ≤ M := by
      rw [hMdef]
      exact le_add_of_nonneg_right (div_nonneg hW0 (by linarith))
    have hMeq : (1 - Real.exp (-(α * (T - t))) *
        (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q)) * (M - p1) =
        waitingSurplus Q pmf alloc p2 α T t p1 := by
      rw [hMdef]
      field_simp
      ring
    have hl : waitingSurplus Q pmf alloc p2 α T t M - waitingSurplus Q pmf alloc p2 α T t p1 ≤
        (∑ q ∈ Finset.range (Q + 1), pmf q * alloc q) *
          (Real.exp (-(α * (T - t))) * (M - p1)) :=
      f7a55159_lip Q pmf alloc p2 _ M p1 hcoef (hcpos t) hM
    have hfM : (0 : ℝ) ∈ Set.Icc
        ((fun x : ℝ => x - p1 - waitingSurplus Q pmf alloc p2 α T t x) p1)
        ((fun x : ℝ => x - p1 - waitingSurplus Q pmf alloc p2 α T t x) M) := by
      simp only [Set.mem_Icc]
      constructor
      · linarith
      · nlinarith
    obtain ⟨ψ, ⟨hψ1, _hψ2⟩, hψ⟩ := intermediate_value_Icc hM hcont.continuousOn hfM
    simp only at hψ
    refine ⟨ψ, ⟨hψ1, by linarith⟩, ?_⟩
    rintro y ⟨_hy1, hy2⟩
    apply hf.injective
    simp only
    linarith
  · intro t ht ψ _hψ1 hψ2 v
    have hf := hstrict t ht
    unfold buysNow
    constructor
    · rintro ⟨_hv1, hv2⟩
      by_contra hlt'
      have hlt := not_le.mp hlt'
      have := hf hlt
      simp only at this
      linarith
    · intro hv
      have := hf.monotone hv
      try simp only at this
      exact ⟨by linarith, by linarith⟩
  · intro ψ hψ t1 ht1 t2 ht2 h12
    obtain ⟨a1, b1⟩ := hψ t1 ht1
    obtain ⟨_a2, b2⟩ := hψ t2 ht2
    have hf := hstrict t2 ht2
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have h1 := hf hlt
    simp only at h1
    have hc : Real.exp (-(α * (T - t1))) ≤ Real.exp (-(α * (T - t2))) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hα (sub_nonneg.mpr h12)])
    have hmono : waitingSurplus Q pmf alloc p2 α T t1 (ψ t1) ≤
        waitingSurplus Q pmf alloc p2 α T t2 (ψ t1) :=
      f7a55159_monoc Q pmf alloc p2 _ _ (ψ t1) hcoef (by linarith) hc
    linarith
