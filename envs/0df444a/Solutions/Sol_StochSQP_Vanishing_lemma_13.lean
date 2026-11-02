-- Prove2me | solution 1 for StochSQP.Vanishing.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:11:37.269267+00:00
-- url     : https://prove2.me/submissions/f0b58345-09a6-4bca-853b-e2453aeafe8f

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model
import Theorems.Thm_StochSQP_Vanishing_lemma_9_projection

open scoped InnerProductSpace RealInnerProductSpace
open StochSQP.Vanishing

namespace StochSQPVanL13Aux

/-- Second-order Taylor bound for a map whose derivative is `K`-Lipschitz on a convex open set. -/
lemma taylor_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}
    (F : E n → G) (X : Set (E n)) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hF : ContDiffOn ℝ 1 F X) (K : ℝ)
    (hK : ∀ x ∈ X, ∀ y ∈ X, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ K * ‖x - y‖)
    (x d : E n) (α : ℝ) (hα : 0 ≤ α) (hx : x ∈ X) (hx' : x + α • d ∈ X) :
    ‖F (x + α • d) - F x - α • fderiv ℝ F x d‖ ≤ K / 2 * α ^ 2 * ‖d‖ ^ 2 := by
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) α, x + t • d ∈ X := by
    intro t ht
    rcases eq_or_lt_of_le hα with h | h
    · have : t = 0 := le_antisymm (h ▸ ht.2) ht.1
      rw [this, zero_smul, add_zero]; exact hx
    · have := hXc.add_smul_mem hx hx' (t := t / α)
        ⟨div_nonneg ht.1 h.le, (div_le_one h).2 ht.2⟩
      rwa [smul_smul, div_mul_cancel₀ _ h.ne'] at this
  have hdiff : ∀ y ∈ X, HasFDerivAt F (fderiv ℝ F y) y := fun y hy =>
    (((hF.differentiableOn one_ne_zero) y hy).differentiableAt (hXo.mem_nhds hy)).hasFDerivAt
  set φ : ℝ → G := fun t => F (x + t • d) - F x - t • fderiv ℝ F x d with hφdef
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) α,
      HasDerivAt φ (fderiv ℝ F (x + t • d) d - fderiv ℝ F x d) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h2 := (hdiff _ (hseg t ht)).comp_hasDerivAt t h1
    have h3 := (hasDerivAt_id t).smul_const (fderiv ℝ F x d)
    have h4 := (h2.sub_const (F x)).sub h3
    simp only [one_smul] at h4
    exact h4
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => K / 2 * ‖d‖ ^ 2 * t ^ 2) (K * ‖d‖ ^ 2 * t) t := by
    intro t
    have h := (hasDerivAt_pow 2 t).const_mul (K / 2 * ‖d‖ ^ 2)
    have e : K / 2 * ‖d‖ ^ 2 * ((2 : ℕ) * t ^ (2 - 1)) = K * ‖d‖ ^ 2 * t := by norm_num; ring
    rw [e] at h
    exact h
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ)
    (a := 0) (b := α) (B := fun t : ℝ => K / 2 * ‖d‖ ^ 2 * t ^ 2)
    (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hφ t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hφdef]) hB
    (by
      intro t ht
      have hyX := hseg t (Set.Ico_subset_Icc_self ht)
      rw [← ContinuousLinearMap.sub_apply]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have := hK _ hyX _ hx
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
      calc ‖fderiv ℝ F (x + t • d) - fderiv ℝ F x‖ * ‖d‖ ≤ K * (t * ‖d‖) * ‖d‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = K * ‖d‖ ^ 2 * t := by ring)
    (Set.right_mem_Icc.2 hα)
  simp only [hφdef] at key
  calc _ ≤ K / 2 * ‖d‖ ^ 2 * α ^ 2 := key
    _ = K / 2 * α ^ 2 * ‖d‖ ^ 2 := by ring

end StochSQPVanL13Aux

open StochSQPVanL13Aux

theorem tau_nonneg_aux {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (R : Run n m) (hR : IsRun P A R) : ∀ k, 0 ≤ R.τ k := by
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA
  have hJd : ∀ k, P.J (R.x k) (R.d k) = P.J (R.x k) (R.v k) := by
    intro k
    obtain ⟨-, -, -, -, -, -, hJu, hdd, -⟩ := hR k
    rw [hdd, map_add, hJu, add_zero]
  have hs0 : ∀ k, 0 ≤ ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖ := by
    intro k
    obtain ⟨-, -, -, -, hcau, -⟩ := hR k
    have h0 := hcau 0 ⟨le_rfl, hω.le⟩
    simp only [zero_smul, add_zero, sub_self, mul_zero] at h0
    exact h0
  -- τ_k ≥ 0
  have hstep : ∀ k, 0 ≤ prev R.τ A.τ₀ k → 0 ≤ R.τ k := by
    intro k hp
    obtain ⟨-, -, -, -, -, -, -, -, hd0, hd1, -⟩ := hR k
    by_cases hd : R.d k = 0
    · rw [(hd0 hd).1]; exact hp
    obtain ⟨htr, -⟩ := hd1 hd
    by_cases hD : ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ 0
    · rw [htr.1 hD]; exact hp
    push_neg at hD
    have h2 := htr.2 hD
    simp only [hJd k] at h2
    by_cases hpt : prev R.τ A.τ₀ k ≤ (1 - A.σ) * (‖P.c (R.x k)‖ -
        ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) / (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)
    · rw [h2.1 hpt]; exact hp
    push_neg at hpt
    rw [h2.2 hpt]
    exact le_min (mul_nonneg (by linarith) hp)
      (div_nonneg (mul_nonneg (by linarith) (hs0 k)) hD.le)
  have hτnn : ∀ k, 0 ≤ R.τ k := by
    intro k
    induction k with
    | zero => exact hstep 0 hτ0.le
    | succ j ih => exact hstep (j + 1) ih
  exact hτnn

set_option maxHeartbeats 1000000 in
theorem solution {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0))
    (h28 : Cond28 A R) :
    ∀ k : ℕ, R.α k * (1 - (1 - A.η) * R.β k) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) -
        R.τ k * (P.f (R.x k) - P.f (R.x k + R.α k • R.d k)) -
        R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤
      ‖P.c (R.x k)‖ - ‖P.c (R.x k + R.α k • R.d k)‖ := by
  have hτnn := tau_nonneg_aux P A hA R hR
  have h9 := StochSQP.Vanishing.lemma_9_projection P A hA X hA1 R hR hX κH ζH hA3 h28
  have hA' := hA
  obtain ⟨hL, hΓ, hτ0, hχ0, hζ0, hξ0, hω, hεv, hεv1, hσ, hσ1, hετ, hετ1, hεχ, hεζ, hεζ1,
    hεξ, hεξ1, hη, hη1, hθ⟩ := hA'
  obtain ⟨hXo, hXc, -, hfC, hcC, -, -, hgL, -, -, hJL, -⟩ := hA1
  -- the derivative of f is L-Lipschitz on X
  have hfL : ∀ x ∈ X, ∀ y ∈ X, ‖fderiv ℝ P.f x - fderiv ℝ P.f y‖ ≤ A.L * ‖x - y‖ := by
    intro x hx y hy
    have e : ∀ z, fderiv ℝ P.f z = InnerProductSpace.toDual ℝ (E n) (P.grad z) := by
      intro z
      simp only [Problem.grad, gradient, LinearIsometryEquiv.apply_symm_apply]
    rw [e, e, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hgL x hx y hy
  intro k
  obtain ⟨hα0, hα1, hαS⟩ := h9 k
  obtain ⟨⟨hβ0, hβ1⟩, -, -, -, -, -, -, -, -, -, hxn⟩ := hR k
  set x := R.x k with hxdef
  set d := R.d k with hddef
  set α := R.α k with hαdef
  set τ := R.τ k with hτdef
  have hx' : x + α • d ∈ X := hxn ▸ hX (k + 1)
  by_cases hd : d = 0
  · rw [hd]; simp [deltaL]
  have hX' := hαS hd
  unfold alphaSuff at hX'
  have hXα := hX'.trans (min_le_left _ _)
  have hd2 : 0 < ‖d‖ ^ 2 := by have := norm_pos_iff.2 hd; positivity
  have hQ : 0 < τ * A.L + A.Γ := by have := mul_nonneg (hτnn k) hL.le; linarith
  rw [le_div_iff₀ (mul_pos hQ hd2)] at hXα
  -- Taylor bounds
  have Tc := taylor_bound P.c X hXo hXc hcC A.Γ hJL x d α hα0.le (hX k) hx'
  have Tf := taylor_bound P.f X hXo hXc hfC A.L hfL x d α hα0.le (hX k) hx'
  rw [Real.norm_eq_abs, abs_le] at Tf
  have hfd : fderiv ℝ P.f x d = ⟪P.grad x, d⟫_ℝ := by
    simp only [Problem.grad, inner_gradient_left]
  rw [smul_eq_mul, hfd] at Tf
  have hJ : fderiv ℝ P.c x = P.J x := rfl
  rw [hJ] at Tc
  -- ‖c(x')‖ ≤ (1-α)‖c‖ + α‖c + J d‖ + Γ/2 α² ‖d‖²
  have hc1 : ‖P.c (x + α • d)‖ ≤ ‖P.c x + α • P.J x d‖ + A.Γ / 2 * α ^ 2 * ‖d‖ ^ 2 := by
    have := norm_add_le (P.c (x + α • d) - P.c x - α • P.J x d) (P.c x + α • P.J x d)
    rw [show P.c (x + α • d) - P.c x - α • P.J x d + (P.c x + α • P.J x d) =
      P.c (x + α • d) by abel] at this
    linarith
  have hc2 : ‖P.c x + α • P.J x d‖ ≤ (1 - α) * ‖P.c x‖ + α * ‖P.c x + P.J x d‖ := by
    have e : P.c x + α • P.J x d = (1 - α) • P.c x + α • (P.c x + P.J x d) := by
      rw [smul_add, sub_smul, one_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg hα0.le]
  -- assemble
  have hτk := hτnn k
  set Δ := deltaL P x τ (R.g k) d with hΔ
  have hΔe : Δ = -τ * ⟪R.g k, d⟫_ℝ + ‖P.c x‖ - ‖P.c x + P.J x d‖ := by
    rw [hΔ]; rfl
  have k1 : α * (α * ((τ * A.L + A.Γ) * ‖d‖ ^ 2)) ≤ α * (2 * (1 - A.η) * R.β k * Δ) :=
    mul_le_mul_of_nonneg_left hXα hα0.le
  have k2 : τ * P.f (x + α • d) ≤ τ * (P.f x + α * ⟪P.grad x, d⟫_ℝ + A.L / 2 * α ^ 2 * ‖d‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith [Tf.2]) hτk
  have hinner : ⟪P.grad x - R.g k, d⟫_ℝ = ⟪P.grad x, d⟫_ℝ - ⟪R.g k, d⟫_ℝ := inner_sub_left _ _ _
  rw [hinner]
  rw [hΔe] at k1 ⊢
  nlinarith
