-- Prove2me | solution 1 for StochFictPlay.DiscreteChoice.argmax_firstOrder_strictConvex
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:25:54.950263+00:00
-- url     : https://prove2.me/submissions/442baaf9-84fd-4f72-8fcf-ed77703b7764

import Mathlib

namespace CexE53a

/-- The quadratic `y ↦ (y 0)^2` on `Fin 1 → ℝ`. -/
noncomputable def Vq : (Fin 1 → ℝ) → ℝ := fun y => (y 0) ^ 2

/-- Its derivative at `y`: `h ↦ 2 * y 0 * h 0`. -/
noncomputable def Dq (y : Fin 1 → ℝ) : (Fin 1 → ℝ) →L[ℝ] ℝ :=
  (2 * y 0) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)

theorem hasFDerivAt_Vq (y : Fin 1 → ℝ) : HasFDerivAt Vq (Dq y) y := by
  have h1 : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) y :=
    hasFDerivAt_apply 0 y
  have h2 := h1.pow 2
  refine h2.congr_fderiv ?_
  unfold Dq
  congr 1
  norm_num

theorem Dq_single (y : Fin 1 → ℝ) :
    Dq y ((Pi.single 0 (1 : ℝ)) : Fin 1 → ℝ) = 2 * y 0 := by
  simp [Dq]

theorem strictConvex_Vq : StrictConvexOn ℝ Set.univ Vq := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hne : x 0 ≠ y 0 := by
    intro h
    apply hxy
    funext i
    fin_cases i
    exact h
  have hpos : 0 < (x 0 - y 0) ^ 2 := by
    have : x 0 - y 0 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  simp only [Vq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_pos ha hb, hpos, mul_pos (mul_pos ha hb) hpos]

theorem cex : ¬ (∀ {n : ℕ} (V : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ))
    (hO : IsOpen O) (hCV : StrictConvexOn ℝ O V)
    (π : Fin n → ℝ) (y_star : Fin n → ℝ) (hys : y_star ∈ O)
    (V' : (Fin n → ℝ) →L[ℝ] ℝ) (hV' : HasFDerivAt V V' y_star)
    (hinj : ∀ y₁ ∈ O, ∀ y₂ ∈ O, ∀ W₁ W₂ : (Fin n → ℝ) →L[ℝ] ℝ,
      HasFDerivAt V W₁ y₁ → HasFDerivAt V W₂ y₂ → W₁ = W₂ → y₁ = y₂),
    (IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O y_star ↔
      (∀ i, π i = V' ((Pi.single i (1 : ℝ)) : Fin n → ℝ))) ∧
      (∀ y ∈ O, IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O y →
        y = y_star)) := by
  intro H
  have hinj : ∀ y₁ ∈ (Set.univ : Set (Fin 1 → ℝ)), ∀ y₂ ∈ (Set.univ : Set (Fin 1 → ℝ)),
      ∀ W₁ W₂ : (Fin 1 → ℝ) →L[ℝ] ℝ,
      HasFDerivAt Vq W₁ y₁ → HasFDerivAt Vq W₂ y₂ → W₁ = W₂ → y₁ = y₂ := by
    intro y₁ _ y₂ _ W₁ W₂ h₁ h₂ hW
    have e₁ : W₁ = Dq y₁ := h₁.unique (hasFDerivAt_Vq y₁)
    have e₂ : W₂ = Dq y₂ := h₂.unique (hasFDerivAt_Vq y₂)
    have key : Dq y₁ ((Pi.single 0 (1 : ℝ)) : Fin 1 → ℝ)
        = Dq y₂ ((Pi.single 0 (1 : ℝ)) : Fin 1 → ℝ) := by
      rw [← e₁, ← e₂, hW]
    rw [Dq_single, Dq_single] at key
    funext i
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue]
    linarith
  have h := (H (n := 1) Vq Set.univ isOpen_univ strictConvex_Vq (fun _ => 0) (fun _ => 1)
    (Set.mem_univ _) (Dq (fun _ => 1)) (hasFDerivAt_Vq _) hinj).2 (fun _ => 0)
    (Set.mem_univ _) ?_
  · have := congrFun h 0
    norm_num at this
  · intro z _
    simp only [mul_zero, Finset.sum_const_zero, zero_sub, Vq]
    have : 0 ≤ (z 0) ^ 2 := sq_nonneg _
    norm_num
    exact this

end CexE53a

theorem solution : ¬ (∀ {n : ℕ} (V : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ))
    (hO : IsOpen O) (hCV : StrictConvexOn ℝ O V)
    (π : Fin n → ℝ) (y_star : Fin n → ℝ) (hys : y_star ∈ O)
    (V' : (Fin n → ℝ) →L[ℝ] ℝ) (hV' : HasFDerivAt V V' y_star)
    (hinj : ∀ y₁ ∈ O, ∀ y₂ ∈ O, ∀ W₁ W₂ : (Fin n → ℝ) →L[ℝ] ℝ,
      HasFDerivAt V W₁ y₁ → HasFDerivAt V W₂ y₂ → W₁ = W₂ → y₁ = y₂),
    (IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O y_star ↔
      (∀ i, π i = V' ((Pi.single i (1 : ℝ)) : Fin n → ℝ))) ∧
      (∀ y ∈ O, IsMaxOn (fun y => Finset.sum Finset.univ (fun i => y i * π i) - V y) O y →
        y = y_star)) := by
  exact CexE53a.cex
