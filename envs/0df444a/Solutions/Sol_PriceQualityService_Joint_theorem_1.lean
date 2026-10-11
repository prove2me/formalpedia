-- Prove2me | solution 1 for PriceQualityService.Joint.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:22:13.689991+00:00
-- url     : https://prove2.me/submissions/c7774389-3070-42e7-a77f-9afc6449e1f0

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace RRAux_PriceQualityService_Joint_theorem_1

open PriceQualityService.Joint

theorem term_le (y u : ℝ) : y * Real.exp u ≤ Real.exp (u + y - 1) := by
  rw [show u + y - 1 = (y - 1) + u by ring, Real.exp_add]
  have := Real.add_one_le_exp (y - 1)
  have hu := Real.exp_pos u
  nlinarith

theorem term_eq (y u : ℝ) (h : y * Real.exp u = Real.exp (u + y - 1)) : y = 1 := by
  by_contra hy
  have := Real.add_one_lt_exp (show y - 1 ≠ 0 from sub_ne_zero.mpr hy)
  rw [show u + y - 1 = (y - 1) + u by ring, Real.exp_add] at h
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

theorem K_sub_L (α a b c s : ℝ) (hc : 0 < c) (q t : ℝ) :
    b ^ 2 * t ^ 2 / (4 * c) + (s - a + α * b / (2 * c)) * t + α ^ 2 / (4 * c) -
      (α * q - c * q ^ 2 - t * (a - b * q) + t * s) = (2 * c * q - α - t * b) ^ 2 / (4 * c) := by
  field_simp; ring

theorem L_le_K (α a b c s : ℝ) (hc : 0 < c) (q t : ℝ) :
    α * q - c * q ^ 2 - t * (a - b * q) + t * s ≤
      b ^ 2 * t ^ 2 / (4 * c) + (s - a + α * b / (2 * c)) * t + α ^ 2 / (4 * c) := by
  have h := K_sub_L α a b c s hc q t
  have : 0 ≤ (2 * c * q - α - t * b) ^ 2 / (4 * c) := by positivity
  linarith

theorem q_of_L_eq_K (α a b c s : ℝ) (hc : 0 < c) (q t : ℝ)
    (h : α * q - c * q ^ 2 - t * (a - b * q) + t * s =
      b ^ 2 * t ^ 2 / (4 * c) + (s - a + α * b / (2 * c)) * t + α ^ 2 / (4 * c)) :
    q = (α + t * b) / (2 * c) := by
  have h1 := K_sub_L α a b c s hc q t
  rw [← h, sub_self] at h1
  have h2 : (2 * c * q - α - t * b) ^ 2 = 0 := by
    have h4 : (4 * c) ≠ 0 := by positivity
    have := (div_eq_zero_iff.mp h1.symm)
    rcases this with h3 | h3
    · exact h3
    · exact absurd h3 h4
  have h3 : 2 * c * q - α - t * b = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  field_simp
  linarith

-- the sum Σ exp(K_i(t_i) - r - 1)
noncomputable def G {N : ℕ} (α a b c s : Fin N → ℝ) (t : Fin N → ℝ) (r : ℝ) : ℝ :=
  ∑ i, Real.exp (durationExponent α a b c s i (t i) - r - 1)

theorem att_le_L {N : ℕ} (α a b c s : Fin N → ℝ) (p q t : Fin N → ℝ) (r : ℝ) (i : Fin N) :
    (markup a b c p q t i - r) * attraction α s p q t i ≤
      Real.exp ((α i * q i - c i * q i ^ 2 - t i * (a i - b i * q i) + t i * s i) - r - 1) := by
  have h1 := term_le (markup a b c p q t i - r) (α i * q i - p i + t i * s i)
  unfold attraction
  refine h1.trans (le_of_eq ?_)
  congr 1; unfold markup; ring

theorem L_le_K_exp {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (q t : Fin N → ℝ)
    (r : ℝ) (i : Fin N) :
    Real.exp ((α i * q i - c i * q i ^ 2 - t i * (a i - b i * q i) + t i * s i) - r - 1) ≤
      Real.exp (durationExponent α a b c s i (t i) - r - 1) := by
  have h2 := L_le_K (α i) (a i) (b i) (c i) (s i) (hc i) (q i) (t i)
  apply Real.exp_le_exp.mpr
  unfold durationExponent
  linarith

theorem profit_le {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (p q t : Fin N → ℝ)
    (r : ℝ) (hr : G α a b c s t r ≤ r) :
    profit α a b c s p q t ≤ r := by
  have hpos := one_add_sum_pos α s p q t
  have hm := prof_mul α a b c s p q t
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (att_le_L α a b c s p q t r i).trans (L_le_K_exp α a b c s hc q t r i))
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  unfold G at hr
  refine le_of_mul_le_mul_right ?_ hpos
  rw [hm]; nlinarith

theorem profit_attained {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (t : Fin N → ℝ)
    (r : ℝ) (hr : r = G α a b c s t r) :
    profit α a b c s
      (fun i => 1 + r + c i * ((α i + t i * b i) / (2 * c i)) ^ 2 +
        t i * (a i - b i * ((α i + t i * b i) / (2 * c i))))
      (fun i => (α i + t i * b i) / (2 * c i)) t = r := by
  set p : Fin N → ℝ := fun i => 1 + r + c i * ((α i + t i * b i) / (2 * c i)) ^ 2 +
        t i * (a i - b i * ((α i + t i * b i) / (2 * c i))) with hp
  set q : Fin N → ℝ := fun i => (α i + t i * b i) / (2 * c i) with hq
  have hm := prof_mul α a b c s p q t
  have hmk : ∀ i, markup a b c p q t i = r + 1 := by
    intro i; simp only [markup, hp]; ring
  have hatt : ∀ i, attraction α s p q t i =
      Real.exp (durationExponent α a b c s i (t i) - r - 1) := by
    intro i; unfold attraction durationExponent; congr 1; simp only [hp, hq]
    have := hc i
    field_simp; ring
  have hG : ∑ i, Real.exp (durationExponent α a b c s i (t i) - r - 1) = r := by
    unfold G at hr; exact hr.symm
  simp only [hmk, hatt, ← Finset.mul_sum, hG] at hm
  have h1 : (0:ℝ) < 1 + r := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      (Real.exp_pos (durationExponent α a b c s i (t i) - r - 1)).le)
    rw [hG] at this; linarith
  have : profit α a b c s p q t * (1 + r) = r * (1 + r) := by rw [hm]; ring
  exact mul_right_cancel₀ h1.ne' this

theorem G_anti {N : ℕ} (α a b c s : Fin N → ℝ) (t : Fin N → ℝ) {r1 r2 : ℝ} (h : r1 ≤ r2) :
    G α a b c s t r2 ≤ G α a b c s t r1 := by
  unfold G
  exact Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (by linarith)

theorem G_nonneg {N : ℕ} (α a b c s : Fin N → ℝ) (t : Fin N → ℝ) (r : ℝ) :
    0 ≤ G α a b c s t r := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

theorem root_unique {N : ℕ} (α a b c s : Fin N → ℝ) (t : Fin N → ℝ) {r1 r2 : ℝ}
    (h1 : r1 = G α a b c s t r1) (h2 : r2 = G α a b c s t r2) : r1 = r2 := by
  rcases le_total r1 r2 with h | h
  · have := G_anti α a b c s t h; linarith
  · have := G_anti α a b c s t h; linarith

theorem root_exists {N : ℕ} (α a b c s : Fin N → ℝ) (t : Fin N → ℝ) :
    ∃ r, r = G α a b c s t r := by
  have hcont : ContinuousOn (fun r : ℝ => r - G α a b c s t r)
      (Set.Icc 0 (G α a b c s t 0)) := by
    unfold G; fun_prop
  have h0 : (0:ℝ) - G α a b c s t 0 ≤ 0 := by have := G_nonneg α a b c s t 0; linarith
  have h1 : 0 ≤ G α a b c s t 0 - G α a b c s t (G α a b c s t 0) := by
    have := G_anti α a b c s t (G_nonneg α a b c s t 0); linarith
  obtain ⟨R, _, hR⟩ := intermediate_value_Icc (G_nonneg α a b c s t 0) hcont ⟨h0, h1⟩
  exact ⟨R, by simp only at hR; linarith⟩

theorem K_identity (A B C u x v : ℝ) :
    (v - x) * (A * u ^ 2 + B * u + C) + (x - u) * (A * v ^ 2 + B * v + C) -
      (v - u) * (A * x ^ 2 + B * x + C) = A * ((v - x) * (x - u) * (v - u)) := by ring

theorem K_le_max (A B C u x v : ℝ) (hA : 0 ≤ A) (hux : u ≤ x) (hxv : x ≤ v) :
    A * x ^ 2 + B * x + C ≤ max (A * u ^ 2 + B * u + C) (A * v ^ 2 + B * v + C) := by
  have hid := K_identity A B C u x v
  have hp : 0 ≤ A * ((v - x) * (x - u) * (v - u)) := by
    apply mul_nonneg hA; apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have m1 := le_max_left (A * u ^ 2 + B * u + C) (A * v ^ 2 + B * v + C)
  have m2 := le_max_right (A * u ^ 2 + B * u + C) (A * v ^ 2 + B * v + C)
  rcases eq_or_lt_of_le (hux.trans hxv) with he | hlt
  · have : x = u := le_antisymm (he ▸ hxv) hux
    subst this; exact m1
  · have e1 := mul_le_mul_of_nonneg_left m1 (show 0 ≤ v - x by linarith)
    have e2 := mul_le_mul_of_nonneg_left m2 (show 0 ≤ x - u by linarith)
    have : (v - u) * (A * x ^ 2 + B * x + C) ≤
        (v - u) * max (A * u ^ 2 + B * u + C) (A * v ^ 2 + B * v + C) := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)

theorem K_endpoint (A B C u x v : ℝ) (hA : 0 ≤ A) (huv : u < v) (hux : u ≤ x) (hxv : x ≤ v)
    (h1 : A * u ^ 2 + B * u + C ≤ A * x ^ 2 + B * x + C)
    (h2 : A * v ^ 2 + B * v + C ≤ A * x ^ 2 + B * x + C) (hAB : A ≠ 0 ∨ B ≠ 0) :
    x = u ∨ x = v := by
  by_contra hne
  push Not at hne
  have hux' : u < x := lt_of_le_of_ne hux (Ne.symm hne.1)
  have hxv' : x < v := lt_of_le_of_ne hxv hne.2
  have hid := K_identity A B C u x v
  have hpos : 0 < (v - x) * (x - u) * (v - u) := by
    apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have e1 : (v - x) * (A * u ^ 2 + B * u + C) ≤ (v - x) * (A * x ^ 2 + B * x + C) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have e2 : (x - u) * (A * v ^ 2 + B * v + C) ≤ (x - u) * (A * x ^ 2 + B * x + C) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hA0 : A * ((v - x) * (x - u) * (v - u)) ≤ 0 := by nlinarith
  have hA' : A = 0 := by
    by_contra hA1
    have : 0 < A * ((v - x) * (x - u) * (v - u)) := mul_pos (lt_of_le_of_ne hA (Ne.symm hA1)) hpos
    linarith
  subst hA'
  rcases hAB with h | h
  · exact h rfl
  · -- linear: B x ≥ B u and B x ≥ B v with u < x < v forces B = 0
    rcases lt_or_gt_of_ne h with hB | hB
    · have : B * x < B * u := by nlinarith
      linarith
    · have : B * x < B * v := by nlinarith
      linarith

theorem sum_eq_of_le {N : ℕ} (f g : Fin N → ℝ) (hfg : ∀ i, f i ≤ g i)
    (hs : ∑ i, g i ≤ ∑ i, f i) : ∀ i, f i = g i := by
  have h0 : ∑ i, (g i - f i) = 0 := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfg i)
    rw [Finset.sum_sub_distrib]; linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hfg i))] at h0
  intro i; have := h0 i (Finset.mem_univ _); linarith

theorem K_eq_quad {N : ℕ} (α a b c s : Fin N → ℝ) (i : Fin N) (τ : ℝ) :
    durationExponent α a b c s i τ = (b i ^ 2 / (4 * c i)) * τ ^ 2 +
      (s i - a i + α i * b i / (2 * c i)) * τ + α i ^ 2 / (4 * c i) := by
  unfold durationExponent; ring

-- the chosen endpoint
noncomputable def tsel {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  if durationExponent α a b c s i ts ≤ durationExponent α a b c s i tl then tl else ts

theorem tsel_max {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ) (i : Fin N)
    (x : ℝ) (hx : x ∈ Set.Icc ts tl) :
    durationExponent α a b c s i x ≤ durationExponent α a b c s i (tsel α a b c s ts tl i) := by
  have hA : 0 ≤ b i ^ 2 / (4 * c i) := by have := hc i; positivity
  have := K_le_max (b i ^ 2 / (4 * c i)) (s i - a i + α i * b i / (2 * c i))
    (α i ^ 2 / (4 * c i)) ts x tl hA hx.1 hx.2
  rw [← K_eq_quad, ← K_eq_quad, ← K_eq_quad] at this
  unfold tsel
  split_ifs with h
  · rwa [max_eq_right h] at this
  · rwa [max_eq_left (le_of_not_ge h)] at this

theorem tsel_ge {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) :
    durationExponent α a b c s i ts ≤ durationExponent α a b c s i (tsel α a b c s ts tl i) ∧
    durationExponent α a b c s i tl ≤ durationExponent α a b c s i (tsel α a b c s ts tl i) := by
  unfold tsel
  split_ifs with h
  · exact ⟨h, le_rfl⟩
  · exact ⟨le_rfl, le_of_not_ge h⟩

theorem G_le_tsel {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (t : Fin N → ℝ) (ht : ∀ i, t i ∈ Set.Icc ts tl) (r : ℝ) :
    G α a b c s t r ≤ G α a b c s (tsel α a b c s ts tl) r := by
  unfold G
  exact Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (by
    have := tsel_max α a b c s hc ts tl i (t i) (ht i); linarith)

end RRAux_PriceQualityService_Joint_theorem_1

open PriceQualityService.Joint in
open RRAux_PriceQualityService_Joint_theorem_1 in
-- Theorem 1, Wang, Ke & Cui
theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts ≤ tl) :
    (∃ (tstar : Fin N → ℝ) (rstar : ℝ),
      (∀ i, tstar i = ts ∨ tstar i = tl) ∧
      rstar = ∑ i, Real.exp (durationExponent α a b c s i (tstar i) - rstar - 1) ∧
      (∀ r : ℝ, r = ∑ i, Real.exp (durationExponent α a b c s i (tstar i) - r - 1) → r = rstar) ∧
      (let qstar : Fin N → ℝ := fun i => (α i + tstar i * b i) / (2 * c i)
       let pstar : Fin N → ℝ := fun i =>
         1 + rstar + c i * qstar i ^ 2 + tstar i * (a i - b i * qstar i)
       (∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
          profit α a b c s p q t ≤ profit α a b c s pstar qstar tstar) ∧
        profit α a b c s pstar qstar tstar = rstar)) ∧
    (∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
      (∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
          profit α a b c s p' q' t' ≤ profit α a b c s p q t) →
      (∀ i, q i = (α i + t i * b i) / (2 * c i)) ∧
      (∀ i, p i = 1 + profit α a b c s p q t + c i * q i ^ 2 + t i * (a i - b i * q i)) ∧
      profit α a b c s p q t =
        ∑ i, Real.exp (durationExponent α a b c s i (t i) - profit α a b c s p q t - 1) ∧
      (ts < tl → ∀ i, (b i ≠ 0 ∨ a i ≠ s i) → t i = ts ∨ t i = tl)) := by
  set T := tsel α a b c s ts tl with hT
  obtain ⟨R, hR⟩ := root_exists α a b c s T
  have hTend : ∀ i, T i = ts ∨ T i = tl := by
    intro i; simp only [hT, tsel]; split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hTbox : ∀ i, T i ∈ Set.Icc ts tl := by
    intro i; rcases hTend i with h | h <;> rw [h]
    · exact ⟨le_rfl, hst⟩
    · exact ⟨hst, le_rfl⟩
  have hval := profit_attained α a b c s hc T R hR
  have hopt : ∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
      profit α a b c s p q t ≤ R := by
    intro p q t ht
    apply profit_le α a b c s hc
    have := G_le_tsel α a b c s hc ts tl t ht R
    rw [← hT] at this
    linarith
  refine ⟨⟨T, R, hTend, hR, fun r hr => root_unique α a b c s T hr hR, ?_⟩, ?_⟩
  · intro qstar pstar
    refine ⟨fun p q t ht => ?_, hval⟩
    rw [hval]; exact hopt p q t ht
  · intro p q t ht hmax
    obtain ⟨r, hr⟩ : ∃ r, profit α a b c s p q t = r := ⟨_, rfl⟩
    rw [hr] at hmax ⊢
    have hrR : r = R := by
      have h1 := hopt p q t ht
      have h2 := hmax (fun i => 1 + R + c i * ((α i + T i * b i) / (2 * c i)) ^ 2 +
        T i * (a i - b i * ((α i + T i * b i) / (2 * c i))))
        (fun i => (α i + T i * b i) / (2 * c i)) T hTbox
      rw [hval] at h2
      linarith
    subst hrR
    -- chain
    have hX := prof_mul α a b c s p q t
    rw [hr] at hX
    have hsum : ∑ i, (markup a b c p q t i - r) * attraction α s p q t i = r := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      linarith
    let f1 : Fin N → ℝ := fun i => (markup a b c p q t i - r) * attraction α s p q t i
    let f2 : Fin N → ℝ := fun i =>
      Real.exp ((α i * q i - c i * q i ^ 2 - t i * (a i - b i * q i) + t i * s i) - r - 1)
    let f3 : Fin N → ℝ := fun i => Real.exp (durationExponent α a b c s i (t i) - r - 1)
    let f4 : Fin N → ℝ := fun i => Real.exp (durationExponent α a b c s i (T i) - r - 1)
    have h12 : ∀ i, f1 i ≤ f2 i := fun i => att_le_L α a b c s p q t r i
    have h23 : ∀ i, f2 i ≤ f3 i := fun i => L_le_K_exp α a b c s hc q t r i
    have h34 : ∀ i, f3 i ≤ f4 i := fun i => Real.exp_le_exp.mpr (by
      have := tsel_max α a b c s hc ts tl i (t i) (ht i); simp only [hT]; linarith)
    have s1 : ∑ i, f1 i = r := hsum
    have s4 : ∑ i, f4 i = r := by simp only [f4]; have h := hR; unfold G at h; exact h.symm
    have S12 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h12 i)
    have S23 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h23 i)
    have S34 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h34 i)
    have e12 := sum_eq_of_le f1 f2 h12 (by linarith)
    have e23 := sum_eq_of_le f2 f3 h23 (by linarith)
    have e34 := sum_eq_of_le f3 f4 h34 (by linarith)
    have hq : ∀ i, q i = (α i + t i * b i) / (2 * c i) := by
      intro i
      have := Real.exp_injective (e23 i)
      apply q_of_L_eq_K (α i) (a i) (b i) (c i) (s i) (hc i)
      unfold durationExponent at this
      linarith
    refine ⟨hq, ?_, ?_, ?_⟩
    · intro i
      have h := e12 i
      simp only [f1, f2] at h
      have hy : markup a b c p q t i - r = 1 := by
        apply term_eq _ (α i * q i - p i + t i * s i)
        unfold attraction at h
        rw [h]; congr 1; unfold markup; ring
      unfold markup at hy
      linarith
    · have : ∑ i, f3 i = r := by linarith
      exact this.symm
    · intro hlt i hi
      have h := Real.exp_injective (e34 i)
      have hK : durationExponent α a b c s i (t i) = durationExponent α a b c s i (T i) := by
        linarith
      obtain ⟨g1, g2⟩ := tsel_ge α a b c s ts tl i
      rw [← hT, ← hK] at g1 g2
      rw [K_eq_quad, K_eq_quad] at g1 g2
      have hA : 0 ≤ b i ^ 2 / (4 * c i) := by have := hc i; positivity
      apply K_endpoint _ _ _ ts (t i) tl hA hlt (ht i).1 (ht i).2 g1 g2
      rcases hi with hb | has
      · left; have := hc i; positivity
      · by_cases hb : b i = 0
        · right; rw [hb]; simp only [mul_zero, zero_div, add_zero]
          exact sub_ne_zero.mpr (Ne.symm has)
        · left; have := hc i; positivity

#print axioms solution
