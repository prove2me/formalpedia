-- Prove2me | solution 1 for PriceQualityService.Joint.duration_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:39:31.730836+00:00
-- url     : https://prove2.me/submissions/6035305c-2d3a-4f80-a15a-037f7146ff6e

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model
set_option autoImplicit false


open PriceQualityService.Joint

lemma pq_hasDeriv (y : ℝ) :
    HasDerivAt (fun y : ℝ => (y + 1) * Real.exp (-y)) (-y * Real.exp (-y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => y + 1) 1 y := (hasDerivAt_id y).add_const 1
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-y) * (-1)) y :=
    (hasDerivAt_neg y).exp
  exact (h1.mul h2).congr_deriv (by ring)

lemma pq_f_mono : StrictMonoOn (fun y : ℝ => (y + 1) * Real.exp (-y)) (Set.Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 0)
  · exact (by fun_prop : Continuous fun y : ℝ => (y + 1) * Real.exp (-y)).continuousOn
  · intro y hy
    rw [interior_Iic] at hy
    rw [(pq_hasDeriv y).deriv]
    have h : y < 0 := hy
    have := Real.exp_pos (-y)
    nlinarith

lemma pq_f_anti : StrictAntiOn (fun y : ℝ => (y + 1) * Real.exp (-y)) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact (by fun_prop : Continuous fun y : ℝ => (y + 1) * Real.exp (-y)).continuousOn
  · intro y hy
    rw [interior_Ici] at hy
    rw [(pq_hasDeriv y).deriv]
    have h : 0 < y := hy
    have := Real.exp_pos (-y)
    nlinarith

lemma pq_f_lt (y : ℝ) (hy : y ≠ 0) : (y + 1) * Real.exp (-y) < 1 := by
  have h := Real.add_one_lt_exp hy
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have := Real.exp_pos (-y)
  nlinarith

lemma pq_f_le (y : ℝ) : (y + 1) * Real.exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have := Real.exp_pos (-y)
  nlinarith

lemma pq_h_eq (x K C : ℝ) :
    (x - K) * Real.exp (C - x) =
      Real.exp (C - K - 1) * (((x - (K + 1)) + 1) * Real.exp (-(x - (K + 1)))) := by
  have : Real.exp (C - x) = Real.exp (C - K - 1) * Real.exp (-(x - (K + 1))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

lemma pq_term_le (x K C : ℝ) : (x - K) * Real.exp (C - x) ≤ Real.exp (C - K - 1) := by
  rw [pq_h_eq]
  have := Real.exp_pos (C - K - 1)
  have := pq_f_le (x - (K + 1))
  nlinarith

lemma pq_term_lt (x K C : ℝ) (hx : x ≠ K + 1) :
    (x - K) * Real.exp (C - x) < Real.exp (C - K - 1) := by
  rw [pq_h_eq]
  have := Real.exp_pos (C - K - 1)
  have := pq_f_lt (x - (K + 1)) (sub_ne_zero.mpr hx)
  nlinarith

lemma pq_term_max (K C : ℝ) : ((K + 1) - K) * Real.exp (C - (K + 1)) = Real.exp (C - K - 1) := by
  have : Real.exp (C - (K + 1)) = Real.exp (C - K - 1) := by congr 1; ring
  rw [this]; ring

lemma pq_root {N : ℕ} (k : Fin N → ℝ) :
    Antitone (fun r : ℝ => ∑ i, Real.exp (k i - r - 1)) ∧
    (0 < N → StrictAnti (fun r : ℝ => ∑ i, Real.exp (k i - r - 1))) ∧
    ∃ r : ℝ, r = ∑ i, Real.exp (k i - r - 1) ∧
      ∀ r' : ℝ, r' = ∑ i, Real.exp (k i - r' - 1) → r' = r := by
  have hanti : Antitone (fun r : ℝ => ∑ i, Real.exp (k i - r - 1)) := by
    intro x y hxy
    apply Finset.sum_le_sum
    intro i _
    apply Real.exp_le_exp.mpr
    linarith
  refine ⟨hanti, ?_, ?_⟩
  · intro hN
    intro x y hxy
    have : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    apply Finset.sum_lt_sum_of_nonempty this
    intro i _
    apply Real.exp_lt_exp.mpr
    linarith
  · set H : ℝ → ℝ := fun r => ∑ i, Real.exp (k i - r - 1) with hH
    have hH0 : 0 ≤ H 0 := Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
    have hHnn : ∀ r, 0 ≤ H r := fun r => Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
    have hcont : Continuous (fun r : ℝ => r - H r) := by
      simp only [hH]; fun_prop
    have hab : (-1 : ℝ) ≤ H 0 + 1 := by linarith
    have hlo : (fun r : ℝ => r - H r) (-1) ≤ 0 := by
      have := hHnn (-1); simp only; linarith
    have hhi : 0 ≤ (fun r : ℝ => r - H r) (H 0 + 1) := by
      have := hanti (show (0 : ℝ) ≤ H 0 + 1 by linarith)
      simp only [hH] at this ⊢
      linarith
    obtain ⟨r, _, hr⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨hlo, hhi⟩
    refine ⟨r, ?_, ?_⟩
    · have : r - H r = 0 := hr
      simp only [hH] at this ⊢
      linarith
    · intro r' hr'
      have hr1 : r = H r := by have : r - H r = 0 := hr; linarith
      rcases lt_trichotomy r' r with h | h | h
      · exfalso
        have := hanti h.le
        have h3 : H r' = r' := hr'.symm
        simp only [hH] at hr1 h3 this
        linarith
      · exact h
      · exfalso
        have := hanti h.le
        have h3 : H r' = r' := hr'.symm
        simp only [hH] at hr1 h3 this
        linarith

lemma pq_mul {N : ℕ} (α a b c s p q t : Fin N → ℝ) :
    profit α a b c s p q t * (1 + ∑ j, attraction α s p q t j) =
      ∑ i, markup a b c p q t i * attraction α s p q t i := by
  have hS : 0 < 1 + ∑ j, attraction α s p q t j := by
    have : 0 ≤ ∑ j, attraction α s p q t j :=
      Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
    linarith
  unfold profit choiceProb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

lemma pq_eq15 {N : ℕ} (α a b c s p q t : Fin N → ℝ) :
    profit α a b c s p q t =
      ∑ i, (markup a b c p q t i - profit α a b c s p q t) *
        Real.exp (α i * q i - p i + t i * s i) := by
  have h1 := pq_mul α a b c s p q t
  have h2 : ∑ i, (markup a b c p q t i - profit α a b c s p q t) *
        Real.exp (α i * q i - p i + t i * s i) =
      ∑ i, markup a b c p q t i * attraction α s p q t i -
        profit α a b c s p q t * ∑ i, attraction α s p q t i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold attraction
    ring
  rw [h2]
  linarith

/-- the profit never exceeds the root. -/
lemma pq_le_root {N : ℕ} (α a b c s q t : Fin N → ℝ) (r : ℝ)
    (hr : r = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r - 1))
    (p : Fin N → ℝ) : profit α a b c s p q t ≤ r := by
  set P := profit α a b c s p q t with hP
  have h15 := pq_eq15 α a b c s p q t
  have hterm : ∀ i, (markup a b c p q t i - P) * Real.exp (α i * q i - p i + t i * s i) ≤
      Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - P - 1) := by
    intro i
    have := pq_term_le (p i) (c i * q i ^ 2 + t i * (a i - b i * q i) + P) (α i * q i + t i * s i)
    have e1 : markup a b c p q t i - P = p i - (c i * q i ^ 2 + t i * (a i - b i * q i) + P) := by
      unfold markup; ring
    have e2 : α i * q i - p i + t i * s i = α i * q i + t i * s i - p i := by ring
    have e3 : α i * q i + t i * s i - (c i * q i ^ 2 + t i * (a i - b i * q i) + P) - 1 =
        α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - P - 1 := by ring
    rw [e1, e2]; rw [e3] at this; exact this
  have hPle : P ≤ ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - P - 1) := by
    calc P = _ := h15
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hterm i)
  by_contra hlt
  push_neg at hlt
  have hanti : Antitone (fun r' : ℝ => ∑ i, Real.exp ((α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i))) - r' - 1)) :=
    (pq_root (fun i => α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)))).1
  have := hanti hlt.le
  simp only at this
  linarith

lemma pq_at_pbar {N : ℕ} (α a b c s q t : Fin N → ℝ) (r : ℝ)
    (hr : r = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r - 1)) :
    profit α a b c s (fun i => 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) q t = r := by
  have hm : ∀ i, markup a b c (fun i => 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) q t i = 1 + r := by
    intro i; unfold markup; ring
  have hA : ∀ i, attraction α s (fun i => 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) q t i =
      Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r - 1) := by
    intro i; unfold attraction; congr 1; ring
  have hsum : ∑ i, attraction α s (fun i => 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) q t i = r := by
    rw [Finset.sum_congr rfl (fun i _ => hA i)]; exact hr.symm
  have hr0 : 0 ≤ r := by rw [hr]; exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have h := pq_mul α a b c s (fun i => 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) q t
  simp_rw [hm] at h
  rw [← Finset.mul_sum, hsum] at h
  have h1 : (1 + r) ≠ 0 := by linarith
  apply mul_right_cancel₀ h1
  linarith

lemma pq_term_le' {N : ℕ} (α a b c s p q t : Fin N → ℝ) (i : Fin N) (P : ℝ) :
    (markup a b c p q t i - P) * Real.exp (α i * q i - p i + t i * s i) ≤
      Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - P - 1) := by
  have := pq_term_le (p i) (c i * q i ^ 2 + t i * (a i - b i * q i) + P) (α i * q i + t i * s i)
  have e1 : markup a b c p q t i - P = p i - (c i * q i ^ 2 + t i * (a i - b i * q i) + P) := by
    unfold markup; ring
  have e2 : α i * q i - p i + t i * s i = α i * q i + t i * s i - p i := by ring
  have e3 : α i * q i + t i * s i - (c i * q i ^ 2 + t i * (a i - b i * q i) + P) - 1 =
      α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - P - 1 := by ring
  rw [e1, e2]; rw [e3] at this; exact this

lemma pq_term_lt' {N : ℕ} (α a b c s p q t : Fin N → ℝ) (i : Fin N) (P : ℝ)
    (hne : p i ≠ c i * q i ^ 2 + t i * (a i - b i * q i) + P + 1) :
    (markup a b c p q t i - P) * Real.exp (α i * q i - p i + t i * s i) <
      Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - P - 1) := by
  have := pq_term_lt (p i) (c i * q i ^ 2 + t i * (a i - b i * q i) + P) (α i * q i + t i * s i) hne
  have e1 : markup a b c p q t i - P = p i - (c i * q i ^ 2 + t i * (a i - b i * q i) + P) := by
    unfold markup; ring
  have e2 : α i * q i - p i + t i * s i = α i * q i + t i * s i - p i := by ring
  have e3 : α i * q i + t i * s i - (c i * q i ^ 2 + t i * (a i - b i * q i) + P) - 1 =
      α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - P - 1 := by ring
  rw [e1, e2]; rw [e3] at this; exact this

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts ≤ tl) (i : Fin N) (r : ℝ) :
    let h : ℝ → ℝ := fun τ => Real.exp (durationExponent α a b c s i τ - r - 1)
    (∀ τ ∈ Set.Icc ts tl, h τ ≤ max (h ts) (h tl)) ∧
      (b i ≠ 0 →
        StrictAntiOn h (Set.Iic ((2 * (a i - s i) * c i - α i * b i) / b i ^ 2)) ∧
          StrictMonoOn h (Set.Ici ((2 * (a i - s i) * c i - α i * b i) / b i ^ 2))) := by
  intro h
  have hci := hc i
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = b i ^ 2 / (4 * c i) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = s i - a i + α i * b i / (2 * c i) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hdiff : ∀ τ σ : ℝ, durationExponent α a b c s i τ - durationExponent α a b c s i σ =
      (τ - σ) * (A * (τ + σ) + B) := by
    intro τ σ
    unfold durationExponent
    rw [hA, hB]; ring
  have hmax : ∀ τ ∈ Set.Icc ts tl,
      durationExponent α a b c s i τ ≤ durationExponent α a b c s i ts ∨
      durationExponent α a b c s i τ ≤ durationExponent α a b c s i tl := by
    intro τ hτ
    rcases le_or_gt (durationExponent α a b c s i τ) (durationExponent α a b c s i ts) with h1 | h1
    · exact Or.inl h1
    · right
      have k1 := hdiff τ ts
      have k2 := hdiff tl τ
      have hτ1 : ts < τ := by
        rcases eq_or_lt_of_le hτ.1 with h2 | h2
        · exfalso; rw [← h2] at h1; exact lt_irrefl _ h1
        · exact h2
      have hpos : 0 < A * (τ + ts) + B := by
        by_contra hneg
        push_neg at hneg
        have : (τ - ts) * (A * (τ + ts) + B) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
        linarith
      have : 0 ≤ (tl - τ) * (A * (tl + τ) + B) := by
        apply mul_nonneg (by linarith [hτ.2])
        nlinarith [hτ.1, hτ.2]
      linarith
  refine ⟨?_, ?_⟩
  · intro τ hτ
    rcases hmax τ hτ with h1 | h1
    · exact le_max_of_le_left (Real.exp_le_exp.mpr (by linarith))
    · exact le_max_of_le_right (Real.exp_le_exp.mpr (by linarith))
  · intro hb
    have hb2 : 0 < b i ^ 2 := by positivity
    have hApos : 0 < A := by rw [hA]; positivity
    obtain ⟨τ0, hτ0⟩ : ∃ τ0 : ℝ, τ0 = (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 := ⟨_, rfl⟩
    have hid : ∀ τ σ : ℝ, durationExponent α a b c s i τ - durationExponent α a b c s i σ =
        A * ((τ - τ0) ^ 2 - (σ - τ0) ^ 2) := by
      intro τ σ
      rw [hdiff]
      have : B = -2 * A * τ0 := by
        rw [hB, hA, hτ0]
        field_simp
        ring
      rw [this]; ring
    rw [← hτ0]
    constructor
    · intro x hx y hy hxy
      have hx' : x ≤ τ0 := hx
      have hy' : y ≤ τ0 := hy
      show Real.exp _ < Real.exp _
      apply Real.exp_lt_exp.mpr
      have := hid y x
      have h3 : (y - τ0) ^ 2 < (x - τ0) ^ 2 := by nlinarith
      nlinarith
    · intro x hx y hy hxy
      have hx' : τ0 ≤ x := hx
      have hy' : τ0 ≤ y := hy
      show Real.exp _ < Real.exp _
      apply Real.exp_lt_exp.mpr
      have := hid y x
      have h3 : (x - τ0) ^ 2 < (y - τ0) ^ 2 := by nlinarith
      nlinarith
