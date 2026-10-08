-- Prove2me | solution 1 for QueueingFundamentals.Foundations.poisson_forward_equations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:43:54.550911+00:00
-- url     : https://prove2.me/submissions/a1481d65-4620-49ec-b630-43d88792a955

import Mathlib



namespace QueueingFundamentals.Foundations

open Set

lemma qfb_uniq (f M c : ℝ → ℝ)
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (-c t * f t) (Ici 0) t)
    (hM : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt M (c t) (Ici 0) t) (h0 : f 0 = 0) :
    ∀ t : ℝ, 0 ≤ t → f t = 0 := by
  intro t ht
  set g : ℝ → ℝ := fun s => f s * Real.exp (M s) with hg
  have hgd : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt g 0 (Ici 0) s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun s => f s * Real.exp (M s))
        (-c s * f s * Real.exp (M s) + f s * (Real.exp (M s) * c s)) (Ici 0) s :=
      (hf s hs).mul ((hM s hs).exp)
    exact h1.congr_deriv (by ring)
  have hcont : ContinuousOn g (Icc 0 t) := by
    intro s hs
    exact ((hgd s hs.1).continuousWithinAt).mono Icc_subset_Ici_self
  have key := constant_of_has_deriv_right_zero hcont (fun s hs =>
    (hgd s hs.1).mono (Ici_subset_Ici.mpr hs.1)) t ⟨ht, le_rfl⟩
  simp only [hg, h0, zero_mul] at key
  have := Real.exp_pos (M t)
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · linarith

/-- q n t = exp(-M t) * M t ^ n / n! -/
lemma qfb_qderiv (lam M : ℝ → ℝ) (t : ℝ)
    (hM : HasDerivWithinAt M (lam t) (Ici 0) t) (n : ℕ) :
    HasDerivWithinAt (fun s => Real.exp (-M s) * M s ^ (n + 1) / ((n + 1).factorial : ℝ))
      (-lam t * (Real.exp (-M t) * M t ^ (n + 1) / ((n + 1).factorial : ℝ)) +
        lam t * (Real.exp (-M t) * M t ^ n / (n.factorial : ℝ))) (Ici 0) t := by
  have hp : HasDerivWithinAt (fun s => M s ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * M t ^ n * lam t)
      (Ici 0) t := by
    have := (hasDerivAt_pow (n + 1) (M t)).comp_hasDerivWithinAt t hM
    exact this.congr_deriv (by push_cast; ring)
  have h1 : HasDerivWithinAt (fun s => Real.exp (-M s) * M s ^ (n + 1) / ((n + 1).factorial : ℝ))
      ((Real.exp (-M t) * -lam t * M t ^ (n + 1) + Real.exp (-M t) * (((n + 1 : ℕ) : ℝ) *
        M t ^ n * lam t)) / ((n + 1).factorial : ℝ)) (Ici 0) t :=
    ((hM.neg).exp.mul hp).div_const ((n + 1).factorial : ℝ)
  refine h1.congr_deriv ?_
  rw [Nat.factorial_succ]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma qfb_core (lam M : ℝ → ℝ) (hM0 : M 0 = 0)
    (hM : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt M (lam t) (Ici 0) t) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam t * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam t * p n t + lam t * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = Real.exp (-M t) * M t ^ n / (n.factorial : ℝ) := by
  constructor
  · rintro ⟨h0, hn, hp0, hpn⟩
    intro n
    induction n with
    | zero =>
      have := qfb_uniq (fun s => p 0 s - Real.exp (-M s)) M lam (fun t ht => by
        have h1 : HasDerivWithinAt (fun s => p 0 s - Real.exp (-M s))
          (-lam t * p 0 t - Real.exp (-M t) * -lam t) (Ici 0) t :=
          (h0 t ht).sub ((hM t ht).neg.exp)
        exact h1.congr_deriv (by ring)) hM (by simp [hp0, hM0])
      intro t ht
      have := this t ht
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]; linarith
    | succ n ih =>
      have := qfb_uniq (fun s => p (n + 1) s - Real.exp (-M s) * M s ^ (n + 1) /
          ((n + 1).factorial : ℝ)) M lam (fun t ht => by
        have h1 := (hn (n + 1) (by omega) t ht).sub (qfb_qderiv lam M t (hM t ht) n)
        simp only [Nat.add_sub_cancel] at h1
        rw [ih t ht] at h1
        exact h1.congr_deriv (by ring)) hM (by simp [hpn (n + 1) (by omega), hM0])
      intro t ht
      have := this t ht
      linarith
  · intro H
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      have h1 := (hM t ht).neg.exp
      have : HasDerivWithinAt (p 0) (Real.exp (-M t) * -lam t) (Ici 0) t := by
        apply h1.congr_of_mem (fun s hs => by rw [H 0 s hs]; simp) ht
      convert this using 1
      rw [H 0 t ht]; simp; ring
    · intro n hn t ht
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h1 := qfb_qderiv lam M t (hM t ht) k
      have : HasDerivWithinAt (p (k + 1)) (-lam t * (Real.exp (-M t) * M t ^ (k + 1) /
          ((k + 1).factorial : ℝ)) + lam t * (Real.exp (-M t) * M t ^ k / (k.factorial : ℝ)))
          (Ici 0) t := h1.congr_of_mem (fun s hs => H (k + 1) s hs) ht
      convert this using 2
      · rw [H (k + 1) t ht]
      · simp only [Nat.add_sub_cancel]; rw [H k t ht]
    · rw [H 0 0 le_rfl, hM0]; simp
    · intro n hn
      rw [H n 0 le_rfl, hM0, zero_pow (by omega)]; simp

theorem poisson_forward_equations_core (lam : ℝ) (hlam : 0 < lam) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam * p n t + lam * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by
  have := qfb_core (fun _ => lam) (fun t => lam * t) (by simp)
    (fun t _ => by simpa using ((hasDerivAt_id t).const_mul lam).hasDerivWithinAt) p
  rw [this]
  apply forall_congr'; intro n; apply forall_congr'; intro t; apply forall_congr'; intro _
  rw [show Real.exp (-(lam * t)) * (lam * t) ^ n / (n.factorial : ℝ) =
    (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) by ring]

theorem nonhomogeneous_poisson_core (lam : ℝ → ℝ) (hcont : ContinuousOn lam (Set.Ici 0))
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ lam t) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam t * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam t * p n t + lam t * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = Real.exp (-(∫ s in (0 : ℝ)..t, lam s)) * (∫ s in (0 : ℝ)..t, lam s) ^ n /
        (n.factorial : ℝ) := by
  apply qfb_core lam (fun t => ∫ s in (0 : ℝ)..t, lam s) (by simp)
  intro t ht
  have hii : IntervalIntegrable lam MeasureTheory.volume 0 t :=
    (hcont.mono (by
      rw [Set.uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
  rcases ht.lt_or_eq with htp | rfl
  · have hmeas : StronglyMeasurableAtFilter lam (nhds t) :=
      (hcont.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t htp
    have hca : ContinuousAt lam t := (hcont t ht).continuousAt (Ici_mem_nhds htp)
    exact (intervalIntegral.integral_hasDerivAt_right hii hmeas hca).hasDerivWithinAt
  · have hmeas : StronglyMeasurableAtFilter lam (nhdsWithin 0 (Ioi 0)) :=
      (hcont.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi 0
    exact intervalIntegral.integral_hasDerivWithinAt_right (s := Ici 0) (t := Ioi 0) hii hmeas
      ((hcont 0 self_mem_Ici).mono Ioi_subset_Ici_self)

end QueueingFundamentals.Foundations

open QueueingFundamentals.Foundations


theorem solution (lam : ℝ) (hlam : 0 < lam) (p : ℕ → ℝ → ℝ) :
    ((∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (p 0) (-lam * p 0 t) (Set.Ici 0) t) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (p n) (-lam * p n t + lam * p (n - 1) t) (Set.Ici 0) t) ∧
      p 0 0 = 1 ∧ (∀ n : ℕ, 0 < n → p n 0 = 0)) ↔
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
      p n t = (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by
  exact poisson_forward_equations_core lam hlam p
