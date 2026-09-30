-- Prove2me | solution 1 for RevenueManagement.deterministic_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:33:18.626217+00:00
-- url     : https://prove2.me/submissions/1820a8e9-9f0d-4e50-8c31-67783a47e1b2

import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

open Finset

/-- A concave function on `[0, 1]` is bounded above there. -/
lemma dub_bdd (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Icc 0 1) f) :
    ∃ M, ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ M := by
  refine ⟨2 * (|f (1 / 2)| + |f 0| + |f 1|), fun x hx => ?_⟩
  obtain ⟨hx0, hx1⟩ := hx
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have a1 := le_abs_self (f (1 / 2))
  have a2 := neg_abs_le (f 0)
  have a3 := neg_abs_le (f 1)
  have a4 := abs_nonneg (f 0)
  have a5 := abs_nonneg (f 1)
  have a6 := abs_nonneg (f (1 / 2))
  rcases le_total x (1 / 2) with hx2 | hx2
  · have hpos : 0 < 1 - x := by linarith
    have hne : 1 - x ≠ 0 := hpos.ne'
    have ha1 : 1 / 2 ≤ 1 / (2 * (1 - x)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    have ha2 : 1 / (2 * (1 - x)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hcomb := hf.2 ⟨hx0, hx1⟩ h1 (by linarith : (0 : ℝ) ≤ 1 / (2 * (1 - x)))
      (by linarith : (0 : ℝ) ≤ 1 - 1 / (2 * (1 - x))) (by ring)
    have hpt : (1 / (2 * (1 - x))) • x + (1 - 1 / (2 * (1 - x))) • (1 : ℝ) = 1 / 2 := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt, smul_eq_mul, smul_eq_mul] at hcomb
    rcases le_total 0 (f x) with hfx | hfx
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hfx,
        mul_nonneg (sub_nonneg.mpr ha2) (by linarith : 0 ≤ f 1 + |f 1|),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / (2 * (1 - x))) a5]
    · linarith
  · have hpos : 0 < x := by linarith
    have hne : x ≠ 0 := hpos.ne'
    have ha1 : 1 / 2 ≤ 1 / (2 * x) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    have ha2 : 1 / (2 * x) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hcomb := hf.2 ⟨hx0, hx1⟩ h0 (by linarith : (0 : ℝ) ≤ 1 / (2 * x))
      (by linarith : (0 : ℝ) ≤ 1 - 1 / (2 * x)) (by ring)
    have hpt : (1 / (2 * x)) • x + (1 - 1 / (2 * x)) • (0 : ℝ) = 1 / 2 := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt, smul_eq_mul, smul_eq_mul] at hcomb
    rcases le_total 0 (f x) with hfx | hfx
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hfx,
        mul_nonneg (sub_nonneg.mpr ha2) (by linarith : 0 ≤ f 0 + |f 0|),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / (2 * x)) a4]
    · linarith

/-- The feasible values of the deterministic problem (5.1) from period `t` on. -/
def dubSet (p : ℕ → ℝ → ℝ) (T t : ℕ) (y : ℝ) : Set ℝ :=
  {w | ∃ d : ℕ → ℝ, (∀ s, d s ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ s ∈ Finset.Icc t T, d s ≤ y ∧
    w = ∑ s ∈ Finset.Icc t T, revenueRate p s (d s)}

lemma dub_det_eq (p : ℕ → ℝ → ℝ) (T t : ℕ) (y : ℝ) :
    deterministicValue p T t y = sSup (dubSet p T t y) := rfl

lemma dub_bddAbove (p : ℕ → ℝ → ℝ) (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t))
    (T t : ℕ) (y : ℝ) : BddAbove (dubSet p T t y) := by
  choose M hM using fun s => dub_bdd _ (hr s)
  refine ⟨∑ s ∈ Finset.Icc t T, M s, ?_⟩
  rintro w ⟨d, hd, -, rfl⟩
  exact sum_le_sum fun s _ => hM s (d s) (hd s)

lemma dub_zero_mem (p : ℕ → ℝ → ℝ) (T t : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (0 : ℝ) ∈ dubSet p T t y :=
  ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩, by simpa using hy, by simp [revenueRate]⟩

lemma dub_nonempty (p : ℕ → ℝ → ℝ) (T t : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (dubSet p T t y).Nonempty :=
  ⟨0, dub_zero_mem p T t y hy⟩

lemma dub_nonneg (p : ℕ → ℝ → ℝ) (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t))
    (T t : ℕ) (y : ℝ) (hy : 0 ≤ y) : 0 ≤ deterministicValue p T t y :=
  le_csSup (dub_bddAbove p hr T t y) (dub_zero_mem p T t y hy)

/-- If `a u + b v ≤ M` for all `u ∈ S₁`, `v ∈ S₂` (`a, b ≥ 0`), then
`a sup S₁ + b sup S₂ ≤ M`. -/
lemma dub_comb {S1 S2 : Set ℝ} (h1 : S1.Nonempty) (h2 : S2.Nonempty) {a b M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ u ∈ S1, ∀ v ∈ S2, a * u + b * v ≤ M) :
    a * sSup S1 + b * sSup S2 ≤ M := by
  have step : ∀ (S : Set ℝ), S.Nonempty → ∀ c N : ℝ, 0 ≤ c → (∀ u ∈ S, c * u ≤ N) →
      c * sSup S ≤ N := by
    intro S hS c N hc hu
    rcases hc.lt_or_eq with hc | hc
    · have hle : sSup S ≤ N / c := csSup_le hS fun u hu' => by
        rw [le_div_iff₀ hc, mul_comm]; exact hu u hu'
      calc c * sSup S ≤ c * (N / c) := mul_le_mul_of_nonneg_left hle hc.le
        _ = N := by field_simp
    · obtain ⟨u, hu'⟩ := hS
      have := hu u hu'
      rw [← hc] at this ⊢
      linarith
  have hv : ∀ v ∈ S2, b * v ≤ M - a * sSup S1 := fun v hv => by
    have := step S1 h1 a (M - b * v) ha fun u hu => by linarith [h u hu v hv]
    linarith
  have := step S2 h2 b (M - a * sSup S1) hb hv
  linarith

/-- One period of the deterministic problem: selling at rate `d` in period `t` and following
the `d`-mixture of plans for capacities `y` and `y + 1` from period `t + 1` on is feasible for
capacity `y + 1` from period `t` on (concavity of the revenue rates). -/
lemma dub_key (p : ℕ → ℝ → ℝ) (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t))
    (T t : ℕ) (htT : t ≤ T) (d : ℝ) (hd : d ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) (hy : 0 ≤ y) :
    revenueRate p t d + (d * deterministicValue p T (t + 1) y +
      (1 - d) * deterministicValue p T (t + 1) (y + 1)) ≤
        deterministicValue p T t (y + 1) := by
  obtain ⟨hd0, hd1⟩ := hd
  have hd1' : 0 ≤ 1 - d := by linarith
  have hIcc : Finset.Icc t T = insert t (Finset.Icc (t + 1) T) :=
    (insert_Icc_add_one_left_eq_Icc htT).symm
  have htn : t ∉ Finset.Icc (t + 1) T := by simp
  have hcomb := dub_comb (dub_nonempty p T (t + 1) y hy)
    (dub_nonempty p T (t + 1) (y + 1) (by linarith)) hd0 hd1'
    (M := deterministicValue p T t (y + 1) - revenueRate p t d) ?_
  · simp only [dub_det_eq] at hcomb ⊢
    linarith
  rintro u ⟨e1, he1, hs1, rfl⟩ v ⟨e2, he2, hs2, rfl⟩
  obtain ⟨e, het, hrest⟩ : ∃ e : ℕ → ℝ, e t = d ∧
      ∀ s, s ≠ t → e s = d * e1 s + (1 - d) * e2 s :=
    ⟨fun s => if s = t then d else d * e1 s + (1 - d) * e2 s, by simp,
      fun s hs => by simp [hs]⟩
  have hrest' : ∀ s ∈ Finset.Icc (t + 1) T, e s = d * e1 s + (1 - d) * e2 s :=
    fun s hs => hrest s fun h => htn (h ▸ hs)
  have he01 : ∀ s, e s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    by_cases hst : s = t
    · rw [hst, het]; exact ⟨hd0, hd1⟩
    · rw [hrest s hst]
      obtain ⟨a0, a1⟩ := he1 s
      obtain ⟨b0, b1⟩ := he2 s
      constructor
      · nlinarith [mul_nonneg hd0 a0, mul_nonneg hd1' b0]
      · nlinarith [mul_le_mul_of_nonneg_left a1 hd0, mul_le_mul_of_nonneg_left b1 hd1']
  have hsum : ∑ s ∈ Finset.Icc t T, e s ≤ y + 1 := by
    rw [hIcc, sum_insert htn, het, sum_congr rfl hrest', sum_add_distrib, ← mul_sum, ← mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hs1 hd0, mul_le_mul_of_nonneg_left hs2 hd1']
  have hmem : ∑ s ∈ Finset.Icc t T, revenueRate p s (e s) ∈ dubSet p T t (y + 1) :=
    ⟨e, he01, hsum, rfl⟩
  have hle := le_csSup (dub_bddAbove p hr T t (y + 1)) hmem
  have hval : d * ∑ s ∈ Finset.Icc (t + 1) T, revenueRate p s (e1 s) +
      (1 - d) * ∑ s ∈ Finset.Icc (t + 1) T, revenueRate p s (e2 s) ≤
        ∑ s ∈ Finset.Icc (t + 1) T, revenueRate p s (e s) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun s hs => ?_
    rw [hrest' s hs]
    have := (hr s).2 (he1 s) (he2 s) hd0 hd1' (by ring)
    simpa only [smul_eq_mul] using this
  have hsplit : ∑ s ∈ Finset.Icc t T, revenueRate p s (e s) =
      revenueRate p t d + ∑ s ∈ Finset.Icc (t + 1) T, revenueRate p s (e s) := by
    rw [hIcc, sum_insert htn, het]
  rw [dub_det_eq]
  linarith

/-- The Bernoulli value with `k ≤ T` periods to go is at most the deterministic value over the
same periods, for every integer inventory. -/
lemma dub_main (p : ℕ → ℝ → ℝ) (T : ℕ)
    (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t)) :
    ∀ k, k ≤ T → ∀ x : ℕ, bernoulliValueGo p T k x ≤ deterministicValue p T (T + 1 - k) x := by
  intro k
  induction k with
  | zero =>
    intro _ x
    rw [bernoulliValueGo.eq_1]
    exact dub_nonneg p hr T _ _ (Nat.cast_nonneg x)
  | succ k ih =>
    intro hk x
    have ht : T + 1 - (k + 1) = T - k := by omega
    have ht' : T + 1 - k = T - k + 1 := by omega
    rw [ht]
    cases x with
    | zero =>
      rw [bernoulliValueGo.eq_2]
      exact dub_nonneg p hr T _ _ (Nat.cast_nonneg _)
    | succ x =>
      rw [bernoulliValueGo.eq_3]
      have ih0 := ih (by omega) x
      have ih1 := ih (by omega) (x + 1)
      rw [ht'] at ih0 ih1
      push_cast at ih1 ⊢
      rw [← le_sub_iff_add_le]
      refine csSup_le ((Set.nonempty_Icc.mpr zero_le_one).image _) ?_
      rintro w ⟨d, hd, rfl⟩
      have hkey := dub_key p hr T (T - k) (by omega) d hd x (Nat.cast_nonneg x)
      have m0 := mul_le_mul_of_nonneg_left ih0 hd.1
      have m1 := mul_le_mul_of_nonneg_left ih1 (sub_nonneg.mpr hd.2)
      linarith

end RevenueManagement

open RevenueManagement

theorem solution (p : ℕ → ℝ → ℝ) (T : ℕ)
    (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t)) (C : ℕ) :
    bernoulliValue p T 1 C ≤ deterministicValue p T 1 C := by
  have h := dub_main p T hr T le_rfl C
  have e : T + 1 - T = 1 := by omega
  rw [e] at h
  have e2 : T + 1 - 1 = T := by omega
  unfold bernoulliValue
  rw [e2]
  exact h
