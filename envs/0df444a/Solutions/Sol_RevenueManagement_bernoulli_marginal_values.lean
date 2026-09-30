-- Prove2me | solution 1 for RevenueManagement.bernoulli_marginal_values
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:37:22.591267+00:00
-- url     : https://prove2.me/submissions/a6043035-10be-48d8-9d7b-806637e7e53a

import Mathlib
import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

/-- `R_f(Δ) = sup_{d ∈ [0,1]} (f d − d Δ)`. -/
noncomputable def bmR (f : ℝ → ℝ) (Δ : ℝ) : ℝ := sSup ((fun d => f d - d * Δ) '' Set.Icc (0 : ℝ) 1)

lemma bm_ne (f : ℝ → ℝ) (Δ : ℝ) : ((fun d => f d - d * Δ) '' Set.Icc (0 : ℝ) 1).Nonempty :=
  ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- Boundedness does not depend on `Δ`. -/
lemma bm_bdd_iff (f : ℝ → ℝ) (a b : ℝ) :
    BddAbove ((fun d => f d - d * a) '' Set.Icc (0 : ℝ) 1) →
      BddAbove ((fun d => f d - d * b) '' Set.Icc (0 : ℝ) 1) := by
  rintro ⟨M, hM⟩
  refine ⟨M + |a| + |b|, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have h1 := hM ⟨d, hd, rfl⟩
  simp only at h1 ⊢
  have ha : -(d * a) ≤ |a| := by
    nlinarith [abs_nonneg a, neg_abs_le a, le_abs_self a, hd.1, hd.2]
  have hb : -(d * b) ≤ |b| := by
    nlinarith [abs_nonneg b, neg_abs_le b, le_abs_self b, hd.1, hd.2]
  have ha' : d * a ≤ |a| := by nlinarith [abs_nonneg a, neg_abs_le a, le_abs_self a, hd.1, hd.2]
  linarith

lemma bm_nonneg (f : ℝ → ℝ) (hf : f 0 = 0) (Δ : ℝ) : 0 ≤ bmR f Δ := by
  by_cases hb : BddAbove ((fun d => f d - d * Δ) '' Set.Icc (0 : ℝ) 1)
  · have := le_csSup hb ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    simp only [hf, zero_mul, sub_zero] at this
    exact this
  · unfold bmR; rw [Real.sSup_of_not_bddAbove hb]

lemma bm_anti (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) : bmR f b ≤ bmR f a := by
  by_cases hb : BddAbove ((fun d => f d - d * a) '' Set.Icc (0 : ℝ) 1)
  · unfold bmR
    apply csSup_le (bm_ne f b)
    rintro _ ⟨d, hd, rfl⟩
    have := le_csSup hb ⟨d, hd, rfl⟩
    simp only at this ⊢
    nlinarith [hd.1]
  · have hb' : ¬ BddAbove ((fun d => f d - d * b) '' Set.Icc (0 : ℝ) 1) :=
      fun h => hb (bm_bdd_iff f b a h)
    unfold bmR; rw [Real.sSup_of_not_bddAbove hb, Real.sSup_of_not_bddAbove hb']

lemma bm_lip (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) : bmR f a ≤ bmR f b + (b - a) := by
  by_cases hb : BddAbove ((fun d => f d - d * b) '' Set.Icc (0 : ℝ) 1)
  · have : bmR f a ≤ bmR f b + (b - a) := by
      apply csSup_le (bm_ne f a)
      rintro _ ⟨d, hd, rfl⟩
      have := le_csSup hb ⟨d, hd, rfl⟩
      simp only at this ⊢
      unfold bmR
      nlinarith [hd.1, hd.2]
    exact this
  · have ha' : ¬ BddAbove ((fun d => f d - d * a) '' Set.Icc (0 : ℝ) 1) :=
      fun h => hb (bm_bdd_iff f a b h)
    unfold bmR; rw [Real.sSup_of_not_bddAbove hb, Real.sSup_of_not_bddAbove ha']; linarith

section
variable (p : ℕ → ℝ → ℝ) (T : ℕ)

local notation "G" => bernoulliValueGo p T

lemma bm_G0 (k : ℕ) : G k 0 = 0 := by
  cases k with
  | zero => exact bernoulliValueGo.eq_1 p T 0
  | succ k => exact bernoulliValueGo.eq_2 p T k

lemma bm_step (k x : ℕ) :
    G (k + 1) (x + 1) = bmR (revenueRate p (T - k)) (G k (x + 1) - G k x) + G k (x + 1) :=
  bernoulliValueGo.eq_3 p T k x

lemma bm_r0 (t : ℕ) : revenueRate p t 0 = 0 := by simp [revenueRate]

/-- `Δ_k(x) = G k x − G k (x − 1)`. -/
noncomputable def bmD (k x : ℕ) : ℝ := G k x - G k (x - 1)

lemma bm_concave : ∀ k x, 1 ≤ x → bmD p T k (x + 1) ≤ bmD p T k x := by
  intro k
  induction k with
  | zero => intro x _; simp [bmD, bernoulliValueGo.eq_1]
  | succ k ih =>
    intro x hx
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    have hab := ih (x' + 1) (by omega)
    simp only [bmD, Nat.add_sub_cancel] at hab ⊢
    rw [bm_step p T k (x' + 1)]
    rcases Nat.eq_zero_or_pos x' with h0 | hpos
    · subst h0
      rw [bm_G0 p T (k + 1), bm_step p T k 0]
      rw [bm_G0 p T k] at hab ⊢
      have hl := bm_lip (revenueRate p (T - k)) hab
      have := bm_nonneg _ (bm_r0 p (T - k)) (G k (0 + 1) - 0)
      linarith
    · obtain ⟨x'', rfl⟩ : ∃ x'', x' = x'' + 1 := ⟨x' - 1, by omega⟩
      rw [bm_step p T k (x'' + 1), bm_step p T k x'']
      have hl := bm_lip (revenueRate p (T - k)) hab
      have hbc := ih (x'' + 1) (by omega)
      simp only [bmD, Nat.add_sub_cancel] at hbc
      have ha := bm_anti (revenueRate p (T - k)) hbc
      linarith

lemma bm_time (k x : ℕ) (hx : 1 ≤ x) : bmD p T k x ≤ bmD p T (k + 1) x := by
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  simp only [bmD, Nat.add_sub_cancel]
  rw [bm_step p T k x']
  rcases Nat.eq_zero_or_pos x' with h0 | hpos
  · subst h0
    rw [bm_G0 p T (k + 1), bm_G0 p T k]
    have := bm_nonneg _ (bm_r0 p (T - k)) (G k (0 + 1) - 0)
    linarith
  · obtain ⟨x'', rfl⟩ : ∃ x'', x' = x'' + 1 := ⟨x' - 1, by omega⟩
    rw [bm_step p T k x'']
    have hbc := bm_concave p T k (x'' + 1) (by omega)
    simp only [bmD, Nat.add_sub_cancel] at hbc
    have := bm_anti (revenueRate p (T - k)) hbc
    linarith

end

end RevenueManagement

open RevenueManagement

theorem solution (p : ℕ → ℝ → ℝ) (T : ℕ)
    (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t)) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (hx : 1 ≤ x) :
    bernoulliDelta p T (t + 1) x ≤ bernoulliDelta p T t x ∧
      bernoulliDelta p T t (x + 1) ≤ bernoulliDelta p T t x := by
  have e1 : T + 1 - (t + 1) = T - t := by omega
  have e2 : T + 1 - t = (T - t) + 1 := by omega
  have hD : ∀ s y, bernoulliDelta p T s y = bmD p T (T + 1 - s) y := fun _ _ => rfl
  rw [hD, hD, hD, e1, e2]
  exact ⟨bm_time p T (T - t) x hx, bm_concave p T (T - t + 1) x hx⟩
