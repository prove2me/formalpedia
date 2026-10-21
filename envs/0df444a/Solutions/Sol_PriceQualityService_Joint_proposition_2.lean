-- Prove2me | solution 1 for PriceQualityService.Joint.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:50:17.172962+00:00
-- url     : https://prove2.me/submissions/7bcb581e-5c1f-4044-9c1a-ee98de151845

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


theorem pqj_quality {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (i : Fin N) (τ r : ℝ) :
    let g : ℝ → ℝ := fun x =>
      Real.exp (α i * x - c i * x ^ 2 + τ * (s i - (a i - b i * x)) - r - 1)
    let qbar : ℝ := (α i + τ * b i) / (2 * c i)
    (∀ x : ℝ, g x ≤ g qbar) ∧ (∀ x : ℝ, g x = g qbar → x = qbar) ∧
      g qbar = Real.exp (durationExponent α a b c s i τ - r - 1) := by
  intro g qbar
  have hci := hc i
  have hid : ∀ x : ℝ, α i * x - c i * x ^ 2 + τ * (s i - (a i - b i * x)) - r - 1 =
      (durationExponent α a b c s i τ - r - 1) - c i * (x - qbar) ^ 2 := by
    intro x
    simp only [durationExponent, qbar]
    field_simp
    ring
  have hg : ∀ x, g x = Real.exp ((durationExponent α a b c s i τ - r - 1) - c i * (x - qbar) ^ 2) := by
    intro x; show Real.exp _ = _; rw [hid]
  have hgq : g qbar = Real.exp (durationExponent α a b c s i τ - r - 1) := by
    rw [hg]; simp
  refine ⟨?_, ?_, hgq⟩
  · intro x
    rw [hg, hgq]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ c i * (x - qbar) ^ 2 := by positivity
    linarith
  · intro x hx
    rw [hg, hgq] at hx
    have := Real.exp_injective hx
    have h2 : c i * (x - qbar) ^ 2 = 0 := by linarith
    have h3 : (x - qbar) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hci.ne'
      · exact h
    have : x - qbar = 0 := by simpa using h3
    linarith


theorem pqj_eq17 {N : ℕ} (α a b c s q t : Fin N → ℝ) :
    ∃ r : ℝ,
      r = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r - 1) ∧
      (∀ r' : ℝ,
        r' = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r' - 1) →
          r' = r) ∧
      (∀ p : Fin N → ℝ, profit α a b c s p q t ≤ r) ∧
      profit α a b c s (fun i => 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) q t = r := by
  obtain ⟨_, _, r, hr, hu⟩ :=
    pq_root (fun i => α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)))
  exact ⟨r, hr, hu, fun p => pq_le_root α a b c s q t r hr p, pq_at_pbar α a b c s q t r hr⟩


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

theorem pqj_duration {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
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




noncomputable def pqjT {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  if b i ≠ 0 then
    (if (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≥ (ts + tl) / 2 then ts else tl)
  else (if a i > s i then ts else tl)

lemma pqj_root_mono {N : ℕ} (k k' : Fin N → ℝ) (hkk : ∀ i, k i ≤ k' i) (r r' : ℝ)
    (hr : r = ∑ i, Real.exp (k i - r - 1)) (hr' : r' = ∑ i, Real.exp (k' i - r' - 1)) : r ≤ r' := by
  by_contra h
  push_neg at h
  have hanti := (pq_root k).1
  have h1 : ∑ i, Real.exp (k i - r - 1) ≤ ∑ i, Real.exp (k i - r' - 1) := hanti h.le
  have h2 : ∑ i, Real.exp (k i - r' - 1) ≤ ∑ i, Real.exp (k' i - r' - 1) :=
    Finset.sum_le_sum (fun i _ => Real.exp_le_exp.2 (by linarith [hkk i]))
  linarith

lemma pqj_root_lt {N : ℕ} (k k' : Fin N → ℝ) (hkk : ∀ i, k i ≤ k' i) (i0 : Fin N)
    (hlt : k i0 < k' i0) (r r' : ℝ)
    (hr : r = ∑ i, Real.exp (k i - r - 1)) (hr' : r' = ∑ i, Real.exp (k' i - r' - 1)) : r < r' := by
  by_contra h
  push_neg at h
  have hanti := (pq_root k).1
  have h1 : ∑ i, Real.exp (k i - r - 1) ≤ ∑ i, Real.exp (k i - r' - 1) := hanti h
  have h2 : ∑ i, Real.exp (k i - r' - 1) < ∑ i, Real.exp (k' i - r' - 1) :=
    Finset.sum_lt_sum (fun i _ => Real.exp_le_exp.2 (by linarith [hkk i]))
      ⟨i0, Finset.mem_univ _, Real.exp_lt_exp.2 (by linarith)⟩
  linarith

lemma pqj_phi_diff {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (i : Fin N) (τ σ : ℝ) :
    durationExponent α a b c s i τ - durationExponent α a b c s i σ =
      (τ - σ) * (b i ^ 2 / (4 * c i) * (τ + σ) + (s i - a i + α i * b i / (2 * c i))) := by
  have := hc i
  unfold durationExponent
  field_simp
  ring

lemma pqj_AB {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (i : Fin N) (hb : b i ≠ 0)
    (x : ℝ) :
    b i ^ 2 / (4 * c i) * x + (s i - a i + α i * b i / (2 * c i)) =
      b i ^ 2 / (4 * c i) * (x - 2 * ((2 * (a i - s i) * c i - α i * b i) / b i ^ 2)) := by
  have := hc i
  field_simp
  ring

lemma pqj_k_le_phi {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (i : Fin N) (x τ : ℝ) :
    α i * x - c i * x ^ 2 + τ * (s i - (a i - b i * x)) ≤ durationExponent α a b c s i τ := by
  have hci := hc i
  have hid : durationExponent α a b c s i τ - (α i * x - c i * x ^ 2 + τ * (s i - (a i - b i * x)))
      = c i * (x - (α i + τ * b i) / (2 * c i)) ^ 2 := by
    unfold durationExponent
    field_simp
    ring
  have : 0 ≤ c i * (x - (α i + τ * b i) / (2 * c i)) ^ 2 := by positivity
  linarith

lemma pqj_k_eq_phi {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (i : Fin N) (τ : ℝ) :
    α i * ((α i + τ * b i) / (2 * c i)) - c i * ((α i + τ * b i) / (2 * c i)) ^ 2
      + τ * (s i - (a i - b i * ((α i + τ * b i) / (2 * c i)))) = durationExponent α a b c s i τ := by
  have hci := hc i
  unfold durationExponent
  field_simp
  ring

lemma pqj_T_mem {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (hst : ts ≤ tl) (i : Fin N) :
    pqjT α a b c s ts tl i ∈ Set.Icc ts tl := by
  unfold pqjT
  split_ifs
  · exact ⟨le_rfl, hst⟩
  · exact ⟨hst, le_rfl⟩
  · exact ⟨le_rfl, hst⟩
  · exact ⟨hst, le_rfl⟩

lemma pqjT_1 {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) (hb : b i ≠ 0)
    (h : (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≥ (ts + tl) / 2) :
    pqjT α a b c s ts tl i = ts := by
  unfold pqjT; rw [if_pos hb, if_pos h]

lemma pqjT_2 {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) (hb : b i ≠ 0)
    (h : ¬ (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≥ (ts + tl) / 2) :
    pqjT α a b c s ts tl i = tl := by
  unfold pqjT; rw [if_pos hb, if_neg h]

lemma pqjT_3 {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) (hb : ¬ b i ≠ 0)
    (h : a i > s i) : pqjT α a b c s ts tl i = ts := by
  unfold pqjT; rw [if_neg hb, if_pos h]

lemma pqjT_4 {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) (hb : ¬ b i ≠ 0)
    (h : ¬ a i > s i) : pqjT α a b c s ts tl i = tl := by
  unfold pqjT; rw [if_neg hb, if_neg h]

lemma pqj_phi_le {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ) (hst : ts ≤ tl)
    (i : Fin N) (τ : ℝ) (hτ : τ ∈ Set.Icc ts tl) :
    durationExponent α a b c s i τ ≤ durationExponent α a b c s i (pqjT α a b c s ts tl i) := by
  have hci := hc i
  have hA0 : 0 ≤ b i ^ 2 / (4 * c i) := by positivity
  have hd := pqj_phi_diff α a b c s hc i
  -- convexity: φ τ ≤ φ ts or φ τ ≤ φ tl
  have hmax : durationExponent α a b c s i τ ≤ durationExponent α a b c s i ts ∨
      durationExponent α a b c s i τ ≤ durationExponent α a b c s i tl := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have e1 := hd τ ts
    have e2 := hd τ tl
    set A : ℝ := b i ^ 2 / (4 * c i)
    set B : ℝ := s i - a i + α i * b i / (2 * c i)
    have hX : 0 < A * (τ + ts) + B := by
      by_contra hX; push_neg at hX
      nlinarith [mul_nonneg (sub_nonneg.2 hτ.1) (neg_nonneg.2 hX)]
    have hY : A * (τ + ts) + B ≤ A * (τ + tl) + B := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hτ.2) (by linarith : 0 ≤ A * (τ + tl) + B)]
  -- the better endpoint
  have hD : durationExponent α a b c s i ts - durationExponent α a b c s i tl =
      -(tl - ts) * (b i ^ 2 / (4 * c i) * (ts + tl) + (s i - a i + α i * b i / (2 * c i))) := by
    rw [hd]; ring
  have hut : 0 ≤ tl - ts := sub_nonneg.2 hst
  have hends : durationExponent α a b c s i ts ≤ durationExponent α a b c s i (pqjT α a b c s ts tl i) ∧
      durationExponent α a b c s i tl ≤ durationExponent α a b c s i (pqjT α a b c s ts tl i) := by
    by_cases hb : b i ≠ 0
    · have hAB := pqj_AB α a b c s hc i hb (ts + tl)
      by_cases hge : (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≥ (ts + tl) / 2
      · rw [pqjT_1 α a b c s ts tl i hb hge]
        refine ⟨le_rfl, ?_⟩
        have hX : b i ^ 2 / (4 * c i) * (ts + tl) + (s i - a i + α i * b i / (2 * c i)) ≤ 0 := by
          rw [hAB]; exact mul_nonpos_of_nonneg_of_nonpos hA0 (by linarith)
        nlinarith [mul_nonneg hut (neg_nonneg.2 hX)]
      · rw [pqjT_2 α a b c s ts tl i hb hge]
        refine ⟨?_, le_rfl⟩
        have hX : 0 ≤ b i ^ 2 / (4 * c i) * (ts + tl) + (s i - a i + α i * b i / (2 * c i)) := by
          rw [hAB]; exact mul_nonneg hA0 (by push_neg at hge; linarith)
        nlinarith [mul_nonneg hut hX]
    · have hb0 : b i = 0 := by simpa using hb
      have hX : b i ^ 2 / (4 * c i) * (ts + tl) + (s i - a i + α i * b i / (2 * c i)) = s i - a i := by
        rw [hb0]; simp
      by_cases hgt : a i > s i
      · rw [pqjT_3 α a b c s ts tl i hb hgt]
        refine ⟨le_rfl, ?_⟩
        rw [hX] at hD
        nlinarith [mul_nonneg hut (by linarith : 0 ≤ a i - s i)]
      · rw [pqjT_4 α a b c s ts tl i hb hgt]
        refine ⟨?_, le_rfl⟩
        rw [hX] at hD
        push_neg at hgt
        nlinarith [mul_nonneg hut (by linarith : 0 ≤ s i - a i)]
  rcases hmax with h | h
  · exact h.trans hends.1
  · exact h.trans hends.2

lemma pqj_phi_lt {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (i : Fin N) (τ : ℝ) (hτ : τ ∈ Set.Icc ts tl)
    (hne : τ ≠ pqjT α a b c s ts tl i)
    (hstrict : (b i ≠ 0 ∧ (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≠ (ts + tl) / 2) ∨
          (b i = 0 ∧ a i ≠ s i)) :
    durationExponent α a b c s i τ < durationExponent α a b c s i (pqjT α a b c s ts tl i) := by
  have hci := hc i
  have hd := pqj_phi_diff α a b c s hc i
  by_cases hb : b i ≠ 0
  · have hc0 : (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≠ (ts + tl) / 2 := by
      rcases hstrict with h | h
      · exact h.2
      · exact absurd h.1 hb
    have hAB := pqj_AB α a b c s hc i hb
    have hApos : 0 < b i ^ 2 / (4 * c i) := by
      have := sq_pos_of_ne_zero hb; positivity
    by_cases hge : (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≥ (ts + tl) / 2
    · have hgt : (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 > (ts + tl) / 2 :=
        lt_of_le_of_ne hge (Ne.symm hc0)
      rw [pqjT_1 α a b c s ts tl i hb hge] at hne ⊢
      have hτts : ts < τ := lt_of_le_of_ne hτ.1 (Ne.symm hne)
      have hneg : b i ^ 2 / (4 * c i) * (τ + ts) + (s i - a i + α i * b i / (2 * c i)) < 0 := by
        rw [hAB]; exact mul_neg_of_pos_of_neg hApos (by linarith [hτ.2])
      have := hd τ ts
      have h2 : (τ - ts) * (b i ^ 2 / (4 * c i) * (τ + ts) + (s i - a i + α i * b i / (2 * c i))) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) hneg
      linarith
    · have hlt : (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 < (ts + tl) / 2 := not_le.1 hge
      rw [pqjT_2 α a b c s ts tl i hb hge] at hne ⊢
      have hτtl : τ < tl := lt_of_le_of_ne hτ.2 hne
      have hpos : 0 < b i ^ 2 / (4 * c i) * (τ + tl) + (s i - a i + α i * b i / (2 * c i)) := by
        rw [hAB]; exact mul_pos hApos (by linarith [hτ.1])
      have := hd τ tl
      have h2 : (τ - tl) * (b i ^ 2 / (4 * c i) * (τ + tl) + (s i - a i + α i * b i / (2 * c i))) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hpos
      linarith
  · have hb0 : b i = 0 := by simpa using hb
    have has : a i ≠ s i := by
      rcases hstrict with h | h
      · exact absurd h.1 hb
      · exact h.2
    have hX : ∀ x, b i ^ 2 / (4 * c i) * x + (s i - a i + α i * b i / (2 * c i)) = s i - a i := by
      intro x; rw [hb0]; simp
    by_cases hgt : a i > s i
    · rw [pqjT_3 α a b c s ts tl i hb hgt] at hne ⊢
      have hτts : ts < τ := lt_of_le_of_ne hτ.1 (Ne.symm hne)
      have := hd τ ts
      rw [hX] at this
      have h2 : (τ - ts) * (s i - a i) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
      linarith
    · rw [pqjT_4 α a b c s ts tl i hb hgt] at hne ⊢
      have hτtl : τ < tl := lt_of_le_of_ne hτ.2 hne
      have hlt : a i < s i := lt_of_le_of_ne (not_lt.1 hgt) has
      have := hd τ tl
      rw [hX] at this
      have h2 : (τ - tl) * (s i - a i) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      linarith

theorem pqj_main {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts ≤ tl) :
    (∃ p q : Fin N → ℝ, ∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
      profit α a b c s p' q' t' ≤ profit α a b c s p q (pqjT α a b c s ts tl)) ∧
    (ts < tl → ∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
      (∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
          profit α a b c s p' q' t' ≤ profit α a b c s p q t) →
      ∀ i, ((b i ≠ 0 ∧ (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≠ (ts + tl) / 2) ∨
          (b i = 0 ∧ a i ≠ s i)) →
        t i = pqjT α a b c s ts tl i) := by
  set T : Fin N → ℝ := pqjT α a b c s ts tl with hT
  have hTmem : ∀ i, T i ∈ Set.Icc ts tl := fun i => pqj_T_mem α a b c s ts tl hst i
  set qs : Fin N → ℝ := fun i => (α i + T i * b i) / (2 * c i) with hqs
  obtain ⟨rs, hrs, _, hle_s, hat_s⟩ := pqj_eq17 α a b c s qs T
  -- comparison of k-vectors
  have hk : ∀ (q' t' : Fin N → ℝ), (∀ i, t' i ∈ Set.Icc ts tl) → ∀ i,
      α i * q' i - c i * q' i ^ 2 + t' i * (s i - (a i - b i * q' i)) ≤
        α i * qs i - c i * qs i ^ 2 + T i * (s i - (a i - b i * qs i)) := by
    intro q' t' ht' i
    have h1 := pqj_k_le_phi α a b c s hc i (q' i) (t' i)
    have h2 := pqj_phi_le α a b c s hc ts tl hst i (t' i) (ht' i)
    have h3 := pqj_k_eq_phi α a b c s hc i (T i)
    rw [hqs]
    simp only
    linarith
  refine ⟨⟨fun i => 1 + rs + c i * qs i ^ 2 + T i * (a i - b i * qs i), qs, ?_⟩, ?_⟩
  · intro p' q' t' ht'
    obtain ⟨r', hr', _, hle', _⟩ := pqj_eq17 α a b c s q' t'
    rw [hat_s]
    refine le_trans (hle' p') ?_
    exact pqj_root_mono _ _ (hk q' t' ht') r' rs hr' hrs
  · intro hlt p q t ht hopt i hstrict
    by_contra hne
    obtain ⟨r, hr, _, hle, _⟩ := pqj_eq17 α a b c s q t
    have hopt' := hopt (fun i => 1 + rs + c i * qs i ^ 2 + T i * (a i - b i * qs i)) qs T hTmem
    rw [hat_s] at hopt'
    have hlt_i : α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) <
        α i * qs i - c i * qs i ^ 2 + T i * (s i - (a i - b i * qs i)) := by
      have h1 := pqj_k_le_phi α a b c s hc i (q i) (t i)
      have h2 := pqj_phi_lt α a b c s hc ts tl i (t i) (ht i) hne hstrict
      have h3 := pqj_k_eq_phi α a b c s hc i (T i)
      rw [hqs]
      simp only
      linarith
    have := pqj_root_lt _ _ (hk q t ht) i hlt_i r rs hr hrs
    have h5 := hle p
    linarith [hopt']

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts ≤ tl) :
    let tstar : Fin N → ℝ := fun i =>
      if b i ≠ 0 then
        (if (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≥ (ts + tl) / 2 then ts else tl)
      else (if a i > s i then ts else tl)
    (∃ p q : Fin N → ℝ, ∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
      profit α a b c s p' q' t' ≤ profit α a b c s p q tstar) ∧
    (ts < tl → ∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
      (∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
          profit α a b c s p' q' t' ≤ profit α a b c s p q t) →
      ∀ i, ((b i ≠ 0 ∧ (2 * (a i - s i) * c i - α i * b i) / b i ^ 2 ≠ (ts + tl) / 2) ∨
          (b i = 0 ∧ a i ≠ s i)) →
        t i = tstar i) := by
  intro tstar
  exact pqj_main α a b c s hc ts tl hst
