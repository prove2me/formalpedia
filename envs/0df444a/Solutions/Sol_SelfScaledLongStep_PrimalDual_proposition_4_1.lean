-- Prove2me | solution 1 for SelfScaledLongStep.PrimalDual.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:04:29.527042+00:00
-- url     : https://prove2.me/submissions/451a5d3b-d573-4db5-a231-9fc2e9d44bda

import Mathlib
set_option autoImplicit false

open Real

lemma p41_log (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun τ : ℝ => Real.log (1 + τ)) (1 / (1 + x)) x := by
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith
  simpa using ((hasDerivAt_id x).const_add 1).log h1

/-- h τ = τ²/(1+τ) - 2τ + 2 log (1+τ) -/
lemma p41_h (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun τ : ℝ => τ ^ 2 / (1 + τ) - 2 * τ + 2 * Real.log (1 + τ))
      (-(x ^ 2) / (1 + x) ^ 2) x := by
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith
  have d1 : HasDerivAt (fun τ : ℝ => τ ^ 2 / (1 + τ))
      ((2 * x * (1 + x) - x ^ 2 * 1) / (1 + x) ^ 2) x := by
    have := (hasDerivAt_pow 2 x).div ((hasDerivAt_id' x).const_add 1) h1
    exact this.congr_deriv (by simp)
  have d2 := ((d1.sub ((hasDerivAt_id' x).const_mul 2)).add ((p41_log x hx).const_mul 2))
  refine d2.congr_deriv ?_
  field_simp
  ring

lemma p41_h_pos (x : ℝ) (hx : 0 < x) :
    x ^ 2 / (1 + x) - 2 * x + 2 * Real.log (1 + x) < 0 := by
  have hanti : StrictAntiOn (fun τ : ℝ => τ ^ 2 / (1 + τ) - 2 * τ + 2 * Real.log (1 + τ))
      (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · intro y hy
      exact (p41_h y (by have : (0:ℝ) ≤ y := hy; linarith)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : (0 : ℝ) < y := hy
      rw [(p41_h y (by linarith)).deriv]
      have : 0 < y ^ 2 := by positivity
      have : 0 < (1 + y) ^ 2 := by positivity
      apply div_neg_of_neg_of_pos <;> linarith
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
  simpa using this

lemma p41_h_neg (x : ℝ) (hx : x < 0) (hx1 : -1 < x) :
    0 < x ^ 2 / (1 + x) - 2 * x + 2 * Real.log (1 + x) := by
  have hanti : StrictAntiOn (fun τ : ℝ => τ ^ 2 / (1 + τ) - 2 * τ + 2 * Real.log (1 + τ))
      (Set.Ioc (-1) 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc (-1) 0)
    · intro y hy
      exact (p41_h y hy.1).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      rw [(p41_h y hy.1).deriv]
      have : 0 < y ^ 2 := by nlinarith [hy.2]
      have : 0 < (1 + y) ^ 2 := by nlinarith [hy.1]
      apply div_neg_of_neg_of_pos <;> linarith
  have := hanti (a := x) (b := 0) ⟨hx1, hx.le⟩ ⟨by norm_num, le_rfl⟩ hx
  simpa using this

/-- k τ = log (1+τ) - τ + τ²/2 -/
lemma p41_k (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun τ : ℝ => Real.log (1 + τ) - τ + τ ^ 2 / 2) (x ^ 2 / (1 + x)) x := by
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith
  have d := ((p41_log x hx).sub (hasDerivAt_id' x)).add ((hasDerivAt_pow 2 x).div_const 2)
  refine d.congr_deriv ?_
  field_simp
  ring

lemma p41_k_pos (x : ℝ) (hx : 0 < x) : 0 < Real.log (1 + x) - x + x ^ 2 / 2 := by
  have hmono : StrictMonoOn (fun τ : ℝ => Real.log (1 + τ) - τ + τ ^ 2 / 2) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro y hy
      exact (p41_k y (by have : (0:ℝ) ≤ y := hy; linarith)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : (0 : ℝ) < y := hy
      rw [(p41_k y (by linarith)).deriv]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
  simpa using this

lemma p41_k_neg (x : ℝ) (hx : x < 0) (hx1 : -1 < x) : Real.log (1 + x) - x + x ^ 2 / 2 < 0 := by
  have hmono : StrictMonoOn (fun τ : ℝ => Real.log (1 + τ) - τ + τ ^ 2 / 2) (Set.Ioc (-1) 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc (-1) 0)
    · intro y hy
      exact (p41_k y hy.1).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      rw [(p41_k y hy.1).deriv]
      have : 0 < 1 + y := by linarith [hy.1]
      have : 0 < y ^ 2 := by nlinarith [hy.2]
      positivity
  have := hmono (a := x) (b := 0) ⟨hx1, hx.le⟩ ⟨by norm_num, le_rfl⟩ hx
  simpa using this

/-- derivative of f τ = (τ - log(1+τ))/τ² at x ≠ 0 -/
lemma p41_f (x : ℝ) (hx : -1 < x) (hx0 : x ≠ 0) :
    HasDerivAt (fun τ : ℝ => (τ - Real.log (1 + τ)) / τ ^ 2)
      ((x ^ 2 / (1 + x) - 2 * x + 2 * Real.log (1 + x)) / x ^ 3) x := by
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith
  have n : HasDerivAt (fun τ : ℝ => τ - Real.log (1 + τ)) (1 - 1 / (1 + x)) x :=
    (hasDerivAt_id' x).sub (p41_log x hx)
  have d := n.div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0)
  refine d.congr_deriv ?_
  beta_reduce
  field_simp
  ring

lemma p41_f_anti_pos : StrictAntiOn (fun τ : ℝ => (τ - Real.log (1 + τ)) / τ ^ 2) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro y hy
    have hy' : (0 : ℝ) < y := hy
    exact (p41_f y (by linarith) hy'.ne').continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    have hy' : (0 : ℝ) < y := hy
    rw [(p41_f y (by linarith) hy'.ne').deriv]
    have := p41_h_pos y hy'
    have : 0 < y ^ 3 := by positivity
    apply div_neg_of_neg_of_pos <;> linarith

lemma p41_f_anti_neg : StrictAntiOn (fun τ : ℝ => (τ - Real.log (1 + τ)) / τ ^ 2) (Set.Ioo (-1) 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (-1) 0)
  · intro y hy
    exact (p41_f y hy.1 hy.2.ne).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioo] at hy
    rw [(p41_f y hy.1 hy.2.ne).deriv]
    have := p41_h_neg y hy.2 hy.1
    have : y ^ 3 < 0 := by
      have : 0 < (-y) ^ 3 := by have : 0 < -y := by linarith [hy.2]
                                positivity
      nlinarith
    exact div_neg_of_pos_of_neg (by linarith) this

lemma p41_f_anti : StrictAntiOn
    (fun τ : ℝ => if τ = 0 then 1 / 2 else (τ - Real.log (1 + τ)) / τ ^ 2) (Set.Ioi (-1)) := by
  have hlt : ∀ x : ℝ, 0 < x → (x - Real.log (1 + x)) / x ^ 2 < 1 / 2 := by
    intro x hx
    have := p41_k_pos x hx
    have hx2 : 0 < x ^ 2 := by positivity
    rw [div_lt_iff₀ hx2]; linarith
  have hgt : ∀ x : ℝ, x < 0 → -1 < x → 1 / 2 < (x - Real.log (1 + x)) / x ^ 2 := by
    intro x hx hx1
    have := p41_k_neg x hx hx1
    have hx2 : 0 < x ^ 2 := by nlinarith
    rw [lt_div_iff₀ hx2]; linarith
  intro a ha b hb hab
  have ha' : -1 < a := ha
  have hb' : -1 < b := hb
  simp only
  rcases lt_trichotomy a 0 with ha0 | ha0 | ha0
  · rcases lt_trichotomy b 0 with hb0 | hb0 | hb0
    · rw [if_neg ha0.ne, if_neg hb0.ne]
      exact p41_f_anti_neg ⟨ha', ha0⟩ ⟨hb', hb0⟩ hab
    · subst hb0
      rw [if_neg ha0.ne, if_pos rfl]
      exact hgt a ha0 ha'
    · rw [if_neg ha0.ne, if_neg hb0.ne']
      exact (hlt b hb0).trans (hgt a ha0 ha')
  · subst ha0
    rw [if_pos rfl, if_neg (by exact hab.ne')]
    exact hlt b hab
  · have hb0 : 0 < b := ha0.trans hab
    rw [if_neg ha0.ne', if_neg hb0.ne']
    exact p41_f_anti_pos ha0 hb0 hab

theorem solution :
    StrictMonoOn (fun τ : ℝ => τ - Real.log (1 + τ)) (Set.Ici 0) ∧
    StrictAntiOn (fun τ : ℝ => if τ = 0 then 1 / 2 else (τ - Real.log (1 + τ)) / τ ^ 2)
      (Set.Ioi (-1)) ∧
    StrictMonoOn (fun τ : ℝ => if τ = 0 then 1 / 2 else (-τ - Real.log (1 - τ)) / τ ^ 2)
      (Set.Iio 1) := by
  refine ⟨?_, p41_f_anti, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro y hy
      have : -1 < y := by have : (0:ℝ) ≤ y := hy; linarith
      have n : HasDerivAt (fun τ : ℝ => τ - Real.log (1 + τ)) (1 - 1 / (1 + y)) y :=
        (hasDerivAt_id' y).sub (p41_log y this)
      exact n.continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : (0 : ℝ) < y := hy
      have n : HasDerivAt (fun τ : ℝ => τ - Real.log (1 + τ)) (1 - 1 / (1 + y)) y :=
        (hasDerivAt_id' y).sub (p41_log y (by linarith))
      rw [n.deriv]
      have : 0 < 1 + y := by linarith
      rw [show (1 : ℝ) - 1 / (1 + y) = y / (1 + y) by field_simp; ring]
      positivity
  · intro a ha b hb hab
    have h := p41_f_anti (a := -b) (b := -a) (by simp at hb ⊢; linarith) (by simp at ha ⊢; linarith)
      (by linarith)
    simp only at h ⊢
    have e : ∀ t : ℝ, (if -t = 0 then (1:ℝ) / 2 else (-t - Real.log (1 + -t)) / (-t) ^ 2)
        = (if t = 0 then 1 / 2 else (-t - Real.log (1 - t)) / t ^ 2) := by
      intro t
      simp [sub_eq_add_neg]
    rw [e, e] at h
    exact h
