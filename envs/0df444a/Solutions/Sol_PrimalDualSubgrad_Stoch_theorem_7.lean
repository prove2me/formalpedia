-- Prove2me | solution 1 for PrimalDualSubgrad.Stoch.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T09:12:01.282696+00:00
-- url     : https://prove2.me/submissions/2e62541e-282f-4852-9575-07b618b12cf0

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting
import Definitions.Def_PrimalDualSubgrad_Stoch_SSA

set_option autoImplicit false

namespace PDSStochAux

open Finset MeasureTheory PrimalDualSubgrad.Stoch

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quadratic growth of a strongly convex objective at its minimizer over `Q`. -/
lemma growth {Q : Set E} {d : E → ℝ} {σ : ℝ} (hsc : StrongConvexOn Q σ d) {β : ℝ} (hβ : 0 < β)
    (S : StrongDual ℝ E) {x1 : E} (hx1 : x1 ∈ Q)
    (hmin : ∀ x ∈ Q, S x1 + β * d x1 ≤ S x + β * d x) (y : E) (hy : y ∈ Q) :
    S x1 + β * d x1 + β * (σ / 2) * ‖y - x1‖ ^ 2 ≤ S y + β * d y := by
  set A := S y + β * d y - (S x1 + β * d x1) with hA
  set B := β * (σ / 2) * ‖y - x1‖ ^ 2 with hB
  have hA0 : 0 ≤ A := by have := hmin y hy; linarith
  have key : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * B ≤ A := by
    intro t ht0 ht1
    have hz := hsc.2 hy hx1 ht0.le (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
    have hm := hmin (t • y + (1 - t) • x1) (hsc.1 hy hx1 ht0.le (by linarith) (by ring))
    have hS : S (t • y + (1 - t) • x1) = t * S y + (1 - t) * S x1 := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hS] at hm
    simp only [smul_eq_mul] at hz
    have h1 := mul_le_mul_of_nonneg_left hz hβ.le
    have h2 : t * ((1 - t) * B) ≤ t * A := by rw [hA, hB]; nlinarith
    exact le_of_mul_le_mul_left h2 ht0
  have hBA : B ≤ A := by
    by_contra hcon
    push_neg at hcon
    have hB0 : 0 < B := lt_of_le_of_lt hA0 hcon
    have := key ((B - A) / (2 * B)) (by apply div_pos <;> linarith)
      (by rw [div_lt_one (by linarith)]; linarith)
    have e : (1 - (B - A) / (2 * B)) * B = (A + B) / 2 := by field_simp; ring
    rw [e] at this; linarith
  linarith

lemma d_nonneg {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0) {x : E}
    (hx : x ∈ Q) : 0 ≤ d x := by
  have := hd.x0_isMin x hx; rw [hd.d_x0] at this; exact this

/-- The argmin condition in the `S + β d` form. -/
lemma argmin_of {Q : Set E} {d : E → ℝ} {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π)
    {β : ℝ} (hβ : 0 < β) (S : StrongDual ℝ E) :
    π β (-S) ∈ Q ∧ ∀ x ∈ Q, S (π β (-S)) + β * d (π β (-S)) ≤ S x + β * d x := by
  obtain ⟨h1, h2⟩ := hπ β hβ (-S)
  refine ⟨h1, fun x hx => ?_⟩
  have := h2 x hx
  simpa [ContinuousLinearMap.neg_apply] using this

/-- Lipschitz continuity of the argmin map. -/
lemma argmin_lip {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {β : ℝ} (hβ : 0 < β)
    (S1 S2 : StrongDual ℝ E) :
    ‖π β (-S1) - π β (-S2)‖ ≤ 1 / (β * σ) * ‖S1 - S2‖ := by
  obtain ⟨m1, h1⟩ := argmin_of hπ hβ S1
  obtain ⟨m2, h2⟩ := argmin_of hπ hβ S2
  set x1 := π β (-S1)
  set x2 := π β (-S2)
  have g1 := growth hd.strongConvexOn hβ S1 m1 h1 x2 m2
  have g2 := growth hd.strongConvexOn hβ S2 m2 h2 x1 m1
  have hσ := hd.sigma_pos
  have hc : 0 < β * σ := mul_pos hβ hσ
  set r := ‖x1 - x2‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr' : ‖x2 - x1‖ = r := norm_sub_rev _ _
  rw [hr'] at g1
  have hlin : (S1 - S2) (x2 - x1) ≤ ‖S1 - S2‖ * r := by
    have := (S1 - S2).le_opNorm (x2 - x1)
    rw [hr'] at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  have hexp : (S1 - S2) (x2 - x1) = S1 x2 - S1 x1 - S2 x2 + S2 x1 := by
    simp [map_sub]; ring
  rw [hexp] at hlin
  have hq : β * σ * r ^ 2 ≤ ‖S1 - S2‖ * r := by linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  rcases hr0.lt_or_eq with hpos | hzero
  · have := le_of_mul_le_mul_right (by nlinarith : r * (β * σ) * r ≤ ‖S1 - S2‖ * r) hpos
    linarith
  · rw [← hzero]; simp [norm_nonneg]

lemma argmin_continuous {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {β : ℝ} (hβ : 0 < β) :
    Continuous (fun S : StrongDual ℝ E => π β (-S)) := by
  refine (LipschitzWith.of_dist_le' (K := 1 / (β * σ)) fun S1 S2 => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact argmin_lip hd hπ hβ S1 S2

/-- Distance of an argmin point from the prox-center. -/
lemma argmin_dist {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {β : ℝ} (hβ : 0 < β)
    (S : StrongDual ℝ E) :
    ‖π β (-S) - x0‖ ≤ 2 / (β * σ) * ‖S‖ := by
  obtain ⟨m1, h1⟩ := argmin_of hπ hβ S
  set x1 := π β (-S)
  have g := growth hd.strongConvexOn hβ S m1 h1 x0 hd.x0_mem
  rw [hd.d_x0] at g
  have hdx := d_nonneg hd m1
  have hσ := hd.sigma_pos
  have hc : 0 < β * σ := mul_pos hβ hσ
  set r := ‖x1 - x0‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr' : ‖x0 - x1‖ = r := norm_sub_rev _ _
  rw [hr'] at g
  have hlin : S (x0 - x1) ≤ ‖S‖ * r := by
    have := S.le_opNorm (x0 - x1)
    rw [hr'] at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  rw [map_sub] at hlin
  have hq : β * σ * r ^ 2 ≤ 2 * (‖S‖ * r) := by nlinarith [mul_nonneg hβ.le hdx]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  rcases hr0.lt_or_eq with hpos | hzero
  · have := le_of_mul_le_mul_right (by nlinarith : r * (β * σ) * r ≤ (2 * ‖S‖) * r) hpos
    linarith
  · rw [← hzero]; simp [norm_nonneg]

lemma betaHat_ge_one : ∀ n, 1 ≤ betaHat n
  | 0 => by simp [betaHat]
  | 1 => by simp [betaHat]
  | (n + 2) => by
    have := betaHat_ge_one (n + 1)
    simp only [betaHat]
    have : 0 ≤ 1 / betaHat (n + 1) := by positivity
    linarith

lemma betaHat_mono (n : ℕ) : betaHat n ≤ betaHat (n + 1) := by
  rcases n with _ | n
  · simp [betaHat]
  · have := betaHat_ge_one (n + 1)
    show betaHat (n + 1) ≤ betaHat (n + 1) + 1 / betaHat (n + 1)
    have : 0 ≤ 1 / betaHat (n + 1) := by positivity
    linarith

lemma betaHat_sum (k : ℕ) : ∑ i ∈ range (k + 1), 1 / betaHat i = betaHat (k + 1) := by
  induction k with
  | zero => simp [betaHat]
  | succ k ih =>
    rw [sum_range_succ, ih]
    show _ = betaHat (k + 1) + 1 / betaHat (k + 1)
    rfl

end Det

section SSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

lemma s_sum (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E) (f' : E → Ξ → StrongDual ℝ E)
    (ω : ℕ → Ξ) : ∀ n, (ssaState π γ x0 f' ω n).2 = ∑ i ∈ range n, f' (ssaRun π γ x0 f' ω i) (ω i)
  | 0 => by simp [ssaState]
  | n + 1 => by rw [sum_range_succ, ← s_sum π γ x0 f' ω n]; rfl

lemma run_succ (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E) (f' : E → Ξ → StrongDual ℝ E)
    (ω : ℕ → Ξ) (n : ℕ) :
    ssaRun π γ x0 f' ω (n + 1) = π (γ * betaHat (n + 1)) (-(ssaState π γ x0 f' ω (n + 1)).2) := rfl

lemma s_succ (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E) (f' : E → Ξ → StrongDual ℝ E)
    (ω : ℕ → Ξ) (n : ℕ) :
    (ssaState π γ x0 f' ω (n + 1)).2 = (ssaState π γ x0 f' ω n).2 + f' (ssaRun π γ x0 f' ω n) (ω n) :=
  rfl

lemma run_mem {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (f' : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) : ∀ n, ssaRun π γ x0 f' ω n ∈ Q
  | 0 => hd.x0_mem
  | n + 1 => by
    rw [run_succ]
    exact (argmin_of hπ (mul_pos hγ (lt_of_lt_of_le one_pos (betaHat_ge_one _))) _).1

lemma run_min {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (f' : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) (n : ℕ) : ∀ x ∈ Q,
    (ssaState π γ x0 f' ω n).2 (ssaRun π γ x0 f' ω n) + γ * betaHat n * d (ssaRun π γ x0 f' ω n)
      ≤ (ssaState π γ x0 f' ω n).2 x + γ * betaHat n * d x := by
  intro x hx
  rcases n with _ | n
  · have h1 : ssaRun π γ x0 f' ω 0 = x0 := rfl
    have h2 : (ssaState π γ x0 f' ω 0).2 = 0 := rfl
    rw [h1, h2, hd.d_x0]
    have := d_nonneg hd hx
    have := betaHat_ge_one 0
    simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_add]
    positivity
  · rw [run_succ]
    exact (argmin_of hπ (mul_pos hγ (lt_of_lt_of_le one_pos (betaHat_ge_one _))) _).2 x hx

/-- Dual-averaging potential lower bound (Nesterov 2009, proof of Theorem 1). -/
lemma potential {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (f' : E → Ξ → StrongDual ℝ E) (L : ℝ) (hL : ∀ x ∈ Q, ∀ ξ, ‖f' x ξ‖ ≤ L) (ω : ℕ → Ξ) :
    ∀ n, ∑ i ∈ range n, (f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i)
        - L ^ 2 / (2 * σ * (γ * betaHat i)))
      ≤ (ssaState π γ x0 f' ω n).2 (ssaRun π γ x0 f' ω n)
          + γ * betaHat n * d (ssaRun π γ x0 f' ω n)
  | 0 => by
    have h1 : ssaRun π γ x0 f' ω 0 = x0 := rfl
    have h2 : (ssaState π γ x0 f' ω 0).2 = 0 := rfl
    simp [h1, h2, hd.d_x0]
  | n + 1 => by
    have ih := potential hd hπ hγ f' L hL ω n
    rw [sum_range_succ]
    set xn := ssaRun π γ x0 f' ω n
    set xn1 := ssaRun π γ x0 f' ω (n + 1)
    set sn := (ssaState π γ x0 f' ω n).2
    set g := f' xn (ω n)
    have hs : (ssaState π γ x0 f' ω (n + 1)).2 = sn + g := s_succ π γ x0 f' ω n
    rw [hs, ContinuousLinearMap.add_apply]
    have hβn : 0 < γ * betaHat n := mul_pos hγ (lt_of_lt_of_le one_pos (betaHat_ge_one _))
    have hmn : xn ∈ Q := run_mem hd hπ hγ f' ω n
    have hmn1 : xn1 ∈ Q := run_mem hd hπ hγ f' ω (n + 1)
    have hgr := growth hd.strongConvexOn hβn sn hmn (run_min hd hπ hγ f' ω n) xn1 hmn1
    have hdn1 := d_nonneg hd hmn1
    have hmono : γ * betaHat n * d xn1 ≤ γ * betaHat (n + 1) * d xn1 := by
      apply mul_le_mul_of_nonneg_right _ hdn1
      exact mul_le_mul_of_nonneg_left (betaHat_mono n) hγ.le
    set r := ‖xn1 - xn‖
    have hr0 : 0 ≤ r := norm_nonneg _
    have hgL : ‖g‖ ≤ L := hL xn hmn (ω n)
    have hg1 : g xn - L * r ≤ g xn1 := by
      have h := g.le_opNorm (xn1 - xn)
      have h' : |g (xn1 - xn)| ≤ L * r :=
        le_trans (by simpa [Real.norm_eq_abs] using h) (mul_le_mul_of_nonneg_right hgL hr0)
      rw [map_sub] at h'
      have := neg_abs_le (g xn1 - g xn)
      linarith
    have hσ := hd.sigma_pos
    set c := γ * betaHat n with hc
    have hcσ : 0 < c * σ := mul_pos hβn hσ
    have amgm : L * r - c * (σ / 2) * r ^ 2 ≤ L ^ 2 / (2 * σ * c) := by
      have h0 : 0 ≤ (c * σ * r - L) ^ 2 / (2 * (c * σ)) := by positivity
      have e : (c * σ * r - L) ^ 2 / (2 * (c * σ))
          = c * (σ / 2) * r ^ 2 - L * r + L ^ 2 / (2 * σ * c) := by
        field_simp; ring
      linarith
    linarith

/-- Pathwise regret bound of SSA. -/
lemma pathwise {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (f' : E → Ξ → StrongDual ℝ E) (L : ℝ) (hL : ∀ x ∈ Q, ∀ ξ, ‖f' x ξ‖ ≤ L) (ω : ℕ → Ξ)
    (xstar : E) (hxstar : xstar ∈ Q) (k : ℕ) :
    ∑ i ∈ range (k + 1), f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - xstar)
      ≤ betaHat (k + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) := by
  have hp := potential hd hπ hγ f' L hL ω (k + 1)
  have hm := run_min hd hπ hγ f' ω (k + 1) xstar hxstar
  have hsum := s_sum π γ x0 f' ω (k + 1)
  have hsx : (ssaState π γ x0 f' ω (k + 1)).2 xstar
      = ∑ i ∈ range (k + 1), f' (ssaRun π γ x0 f' ω i) (ω i) xstar := by
    rw [hsum, ContinuousLinearMap.sum_apply]
  rw [hsx] at hm
  rw [sum_sub_distrib] at hp
  have hL2 : ∑ i ∈ range (k + 1), L ^ 2 / (2 * σ * (γ * betaHat i))
      = L ^ 2 / (2 * σ * γ) * betaHat (k + 1) := by
    rw [← betaHat_sum k, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have := betaHat_ge_one i
    have := hd.sigma_pos
    field_simp
  rw [hL2] at hp
  simp only [map_sub]
  rw [sum_sub_distrib]
  nlinarith

/-- Pathwise loss bound: `∑ (f(x_i, ξ_i) - f(x*, ξ_i)) ≤ β̂_{k+1}(γ d(x*) + L²/(2σγ))`. -/
lemma pathwise_loss {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E) (L : ℝ)
    (hL : ∀ x ∈ Q, ∀ ξ, ‖f' x ξ‖ ≤ L)
    (hsub : ∀ x ∈ Q, ∀ ξ, ∀ y ∈ Q, f x ξ + f' x ξ (y - x) ≤ f y ξ) (ω : ℕ → Ξ)
    (xstar : E) (hxstar : xstar ∈ Q) (k : ℕ) :
    ∑ i ∈ range (k + 1), (f (ssaRun π γ x0 f' ω i) (ω i) - f xstar (ω i))
      ≤ betaHat (k + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) := by
  refine le_trans (sum_le_sum fun i _ => ?_) (pathwise hd hπ hγ f' L hL ω xstar hxstar k)
  have h := hsub _ (run_mem hd hπ hγ f' ω i) (ω i) xstar hxstar
  have e : f' (ssaRun π γ x0 f' ω i) (ω i) (xstar - ssaRun π γ x0 f' ω i)
      = -(f' (ssaRun π γ x0 f' ω i) (ω i) (ssaRun π γ x0 f' ω i - xstar)) := by
    rw [← map_neg, neg_sub]
  rw [e] at h
  linarith

end SSA

section Meas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- A weakly measurable dual-valued map is measurable (finite dimension). -/
lemma dual_meas {Ω : Type*} [MeasurableSpace Ω] (s : Ω → StrongDual ℝ E)
    (hs : ∀ y : E, Measurable fun o => s o y) : Measurable s := by
  let b := Module.finBasis ℝ E
  let T : StrongDual ℝ E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    { toFun := fun φ j => φ (b j)
      map_add' := fun φ ψ => by ext j; simp
      map_smul' := fun c φ => by ext j; simp }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    have h : ∀ j, φ (b j) = 0 := fun j => by simpa [T] using congrFun hφ j
    ext x
    rw [ContinuousLinearMap.zero_apply, ← b.sum_repr x, map_sum]
    simp only [map_smul, h, smul_zero, Finset.sum_const_zero]
  have hemb : MeasurableEmbedding T :=
    (LinearMap.isClosedEmbedding_of_injective hker).measurableEmbedding
  rw [← hemb.measurable_comp_iff]
  exact measurable_pi_lambda _ fun j => hs (b j)

lemma state_meas {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (f' : E → Ξ → StrongDual ℝ E) (hf' : ∀ y : E, Measurable (fun p : E × Ξ => f' p.1 p.2 y))
    {Ω : Type*} [MeasurableSpace Ω] (w : Ω → ℕ → Ξ) (hw : ∀ j, Measurable fun o => w o j) :
    ∀ n, Measurable (fun o => ssaRun π γ x0 f' (w o) n) ∧
      Measurable (fun o => (ssaState π γ x0 f' (w o) n).2)
  | 0 => ⟨show Measurable (fun _ => x0) from measurable_const,
      show Measurable (fun _ => (0 : StrongDual ℝ E)) from measurable_const⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := state_meas hd hπ hγ f' hf' w hw n
    have hs : Measurable (fun o => (ssaState π γ x0 f' (w o) (n + 1)).2) := by
      apply dual_meas
      intro y
      simp only [s_succ, ContinuousLinearMap.add_apply]
      exact ((ContinuousLinearMap.measurable_apply y).comp h2).add
        ((hf' y).comp (h1.prodMk (hw n)))
    refine ⟨?_, hs⟩
    simp only [run_succ]
    exact (argmin_continuous hd hπ
      (mul_pos hγ (lt_of_lt_of_le one_pos (betaHat_ge_one _)))).measurable.comp hs

lemma pad_meas {k : ℕ} (j : ℕ) : Measurable (fun ω : Fin (k + 1) → Ξ => padSample ω j) := by
  by_cases h : j < k + 1
  · have : (fun ω : Fin (k + 1) → Ξ => padSample ω j) = fun ω => ω ⟨j, h⟩ := by
      funext ω; simp [padSample, h]
    rw [this]; exact measurable_pi_apply _
  · have : (fun ω : Fin (k + 1) → Ξ => padSample ω j) = fun ω => ω 0 := by
      funext ω; simp [padSample, h]
    rw [this]; exact measurable_pi_apply _

lemma state_dep (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E) (f' : E → Ξ → StrongDual ℝ E) :
    ∀ n (ω ω' : ℕ → Ξ), (∀ j < n, ω j = ω' j) →
      ssaState π γ x0 f' ω n = ssaState π γ x0 f' ω' n
  | 0, _, _, _ => rfl
  | n + 1, ω, ω', h => by
    have ih := state_dep π γ x0 f' n ω ω' (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hn := h n (Nat.lt_succ_self n)
    simp only [ssaState, ih, hn]

/-- One coordinate of the product sample: `E[h(X, ξ_i)] = E[∫ h(X, ξ) dμ]` when `X` only reads
coordinates `< i`. -/
lemma fubini_step (μ : Measure Ξ) [IsProbabilityMeasure μ] (k : ℕ) (i : Fin (k + 1))
    (X : (ℕ → Ξ) → E) (hX : ∀ ω ω' : ℕ → Ξ, (∀ j < (i : ℕ), ω j = ω' j) → X ω = X ω')
    (h : E → Ξ → ℝ)
    (hint1 : Integrable (fun ω => ∫ ξ, h (X (padSample ω)) ξ ∂μ) (sampleLaw μ k))
    (hint2 : Integrable (fun ω => h (X (padSample ω)) (ω i)) (sampleLaw μ k)) :
    ∫ ω, ∫ ξ, h (X (padSample ω)) ξ ∂μ ∂(sampleLaw μ k)
      = ∫ ω, h (X (padSample ω)) (ω i) ∂(sampleLaw μ k) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Ξ) i with he
  have hmp : MeasurePreserving e (sampleLaw μ k) (μ.prod (Measure.pi fun _ : Fin k => μ)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) i
  have hmps := hmp.symm
  set F1 := fun ω : Fin (k + 1) → Ξ => ∫ ξ, h (X (padSample ω)) ξ ∂μ with hF1
  set F2 := fun ω : Fin (k + 1) → Ξ => h (X (padSample ω)) (ω i) with hF2
  have hdiag : ∀ ξ (ω' : Fin k → Ξ), (e.symm (ξ, ω')) i = ξ := by
    intro ξ ω'; simp [e]
  have hoff : ∀ ξ ζ (ω' : Fin k → Ξ) (m : Fin (k + 1)), m ≠ i →
      (e.symm (ξ, ω')) m = (e.symm (ζ, ω')) m := by
    intro ξ ζ ω' m hm
    obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
    simp [e, Fin.insertNth_apply_succAbove]
  have hsame : ∀ ξ ζ (ω' : Fin k → Ξ),
      X (padSample (e.symm (ξ, ω'))) = X (padSample (e.symm (ζ, ω'))) := by
    intro ξ ζ ω'
    apply hX
    intro j hj
    have hjk : j < k + 1 := lt_trans hj i.isLt
    simp only [padSample, hjk, dif_pos]
    apply hoff
    intro heq
    have := congrArg Fin.val heq
    simp at this
    omega
  have hi1 : Integrable (F1 ∘ e.symm) (μ.prod (Measure.pi fun _ : Fin k => μ)) :=
    (hmps.integrable_comp_emb e.symm.measurableEmbedding).mpr hint1
  have hi2 : Integrable (F2 ∘ e.symm) (μ.prod (Measure.pi fun _ : Fin k => μ)) :=
    (hmps.integrable_comp_emb e.symm.measurableEmbedding).mpr hint2
  calc ∫ ω, F1 ω ∂(sampleLaw μ k)
      = ∫ p, (F1 ∘ e.symm) p ∂(μ.prod (Measure.pi fun _ : Fin k => μ)) :=
        (hmps.integral_comp' F1).symm
    _ = ∫ ω', ∫ ξ, (F1 ∘ e.symm) (ξ, ω') ∂μ ∂(Measure.pi fun _ : Fin k => μ) :=
        integral_prod_symm _ hi1
    _ = ∫ ω', ∫ ξ, (F2 ∘ e.symm) (ξ, ω') ∂μ ∂(Measure.pi fun _ : Fin k => μ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω' => ?_)
        set c := ∫ ξ, (F2 ∘ e.symm) (ξ, ω') ∂μ with hc
        have hpt : ∀ ζ, (F1 ∘ e.symm) (ζ, ω') = c := by
          intro ζ
          simp only [Function.comp, hF1, hF2, hc]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          simp only [hdiag]
          rw [hsame ζ ξ ω']
        simp only [hpt, integral_const, probReal_univ, one_smul]
        exact hc
    _ = ∫ p, (F2 ∘ e.symm) p ∂(μ.prod (Measure.pi fun _ : Fin k => μ)) :=
        (integral_prod_symm _ hi2).symm
    _ = ∫ ω, F2 ω ∂(sampleLaw μ k) := hmps.integral_comp' F2

lemma lip_f {Q : Set E} (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E) (L : ℝ)
    (hL : ∀ x ∈ Q, ∀ ξ, ‖f' x ξ‖ ≤ L)
    (hsub : ∀ x ∈ Q, ∀ ξ, ∀ y ∈ Q, f x ξ + f' x ξ (y - x) ≤ f y ξ)
    (xstar : E) (hxstar : xstar ∈ Q) (x : E) (hx : x ∈ Q) (ξ : Ξ) :
    |f x ξ - f xstar ξ| ≤ L * ‖x - xstar‖ := by
  have h1 := hsub x hx ξ xstar hxstar
  have h2 := hsub xstar hxstar ξ x hx
  have b1 : |f' x ξ (xstar - x)| ≤ L * ‖x - xstar‖ := by
    have := (f' x ξ).le_opNorm (xstar - x)
    rw [norm_sub_rev] at this
    exact le_trans (by simpa [Real.norm_eq_abs] using this)
      (mul_le_mul_of_nonneg_right (hL x hx ξ) (norm_nonneg _))
  have b2 : |f' xstar ξ (x - xstar)| ≤ L * ‖x - xstar‖ := by
    have := (f' xstar ξ).le_opNorm (x - xstar)
    exact le_trans (by simpa [Real.norm_eq_abs] using this)
      (mul_le_mul_of_nonneg_right (hL xstar hxstar ξ) (norm_nonneg _))
  rw [abs_le]
  constructor
  · have := neg_abs_le (f' xstar ξ (x - xstar)); linarith
  · have := neg_le_abs (f' x ξ (xstar - x)); linarith

end Meas

end PDSStochAux

open Finset MeasureTheory PrimalDualSubgrad.Stoch in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (f : E → Ξ → ℝ) (f' : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : StochOracle Q μ f f' L)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, expectedCost μ f xstar ≤ expectedCost μ f x)
    (γ : ℝ) (hγ : 0 < γ) (k : ℕ) :
    ∫ ω, expectedCost μ f ((1 / ((k : ℝ) + 1)) • ∑ i ∈ range (k + 1), ssaRun π γ x0 f' (padSample ω) i)
        ∂(sampleLaw μ k) - expectedCost μ f xstar
      ≤ betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) := by
  classical
  haveI hP : IsProbabilityMeasure (sampleLaw μ k) := by unfold sampleLaw; infer_instance
  let X : ℕ → (Fin (k + 1) → Ξ) → E := fun i ω => ssaRun π γ x0 f' (padSample ω) i
  let ψ : E → ℝ := fun x => ∫ ξ, (f x ξ - f xstar ξ) ∂μ
  let C : ℝ := betaHat (k + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ))
  let w : ℝ := 1 / ((k : ℝ) + 1)
  show ∫ ω, expectedCost μ f (w • ∑ i ∈ range (k + 1), X i ω) ∂(sampleLaw μ k)
      - expectedCost μ f xstar ≤ betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ))
  set P := sampleLaw μ k with hPdef
  have hψφ : ∀ x ∈ Q, ψ x = expectedCost μ f x - expectedCost μ f xstar := fun x hx =>
    integral_sub (hf.integrable x hx) (hf.integrable xstar hxstar)
  have hψmeas : Measurable ψ := by
    have hsm : StronglyMeasurable (fun p : E × Ξ => f p.1 p.2 - f xstar p.2) :=
      (hf.meas_f.sub (hf.meas_f.comp (measurable_const.prodMk measurable_snd))).stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := μ)).measurable
  have hlip : ∀ x ∈ Q, ∀ ξ, |f x ξ - f xstar ξ| ≤ L * ‖x - xstar‖ := fun x hx ξ =>
    PDSStochAux.lip_f f f' L hf.bound hf.subgrad xstar hxstar x hx ξ
  have hψbd : ∀ x ∈ Q, |ψ x| ≤ L * ‖x - xstar‖ := by
    intro x hx
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ξ => f x ξ - f xstar ξ)
      (C := L * ‖x - xstar‖)
      (Filter.Eventually.of_forall fun ξ => by simpa [Real.norm_eq_abs] using hlip x hx ξ)
    simpa [Real.norm_eq_abs, probReal_univ] using this
  have hψnn : ∀ x ∈ Q, 0 ≤ ψ x := fun x hx => by rw [hψφ x hx]; linarith [hmin x hx]
  have hXmeas : ∀ i, Measurable (X i) := fun i =>
    (PDSStochAux.state_meas hd hπ hγ f' hf.meas_f' (fun ω : Fin (k + 1) → Ξ => padSample ω)
      (fun j => PDSStochAux.pad_meas (k := k) j) i).1
  have hXmem : ∀ i ω, X i ω ∈ Q := fun i ω => PDSStochAux.run_mem hd hπ hγ f' (padSample ω) i
  have hXbd : ∀ i, ∃ R, ∀ ω, ‖X i ω - xstar‖ ≤ R := by
    intro i
    rcases i with _ | n
    · exact ⟨‖x0 - xstar‖, fun ω => le_rfl⟩
    · refine ⟨2 / (γ * betaHat (n + 1) * σ) * (((n : ℝ) + 1) * L) + ‖x0 - xstar‖, fun ω => ?_⟩
      have hβ : 0 < γ * betaHat (n + 1) :=
        mul_pos hγ (lt_of_lt_of_le one_pos (PDSStochAux.betaHat_ge_one _))
      have h1 := PDSStochAux.argmin_dist hd hπ hβ (ssaState π γ x0 f' (padSample ω) (n + 1)).2
      have hs : ‖(ssaState π γ x0 f' (padSample ω) (n + 1)).2‖ ≤ ((n : ℝ) + 1) * L := by
        rw [PDSStochAux.s_sum]
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (sum_le_sum fun i _ => hf.bound _ (PDSStochAux.run_mem hd hπ hγ f' _ i) _) ?_
        simp
      have hc : 0 ≤ 2 / (γ * betaHat (n + 1) * σ) := by have := hd.sigma_pos; positivity
      have h3 : ‖X (n + 1) ω - x0‖ ≤ 2 / (γ * betaHat (n + 1) * σ) * (((n : ℝ) + 1) * L) :=
        le_trans h1 (mul_le_mul_of_nonneg_left hs hc)
      have h2 : X (n + 1) ω - xstar = (X (n + 1) ω - x0) + (x0 - xstar) := by abel
      rw [h2]
      refine le_trans (norm_add_le _ _) ?_
      linarith
  have hbound_int : ∀ g : (Fin (k + 1) → Ξ) → ℝ, Measurable g → (∃ R, ∀ ω, |g ω| ≤ R) →
      Integrable g P := by
    rintro g hg ⟨R, hR⟩
    exact Integrable.of_bound hg.aestronglyMeasurable R
      (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hR ω)
  have habsL : ∀ (a R : ℝ), 0 ≤ a → a ≤ R → L * a ≤ |L| * R := fun a R ha haR =>
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self L) ha)
      (mul_le_mul_of_nonneg_left haR (abs_nonneg L))
  have hψX_int : ∀ i, Integrable (fun ω => ψ (X i ω)) P := by
    intro i
    obtain ⟨R, hR⟩ := hXbd i
    exact hbound_int _ (hψmeas.comp (hXmeas i)) ⟨|L| * R, fun ω =>
      le_trans (hψbd _ (hXmem i ω)) (habsL _ _ (norm_nonneg _) (hR ω))⟩
  let H : ℕ → (Fin (k + 1) → Ξ) → ℝ := fun i ω =>
    f (X i ω) (padSample ω i) - f xstar (padSample ω i)
  have hH_int : ∀ i, Integrable (H i) P := by
    intro i
    obtain ⟨R, hR⟩ := hXbd i
    have hm : Measurable (H i) :=
      (hf.meas_f.comp ((hXmeas i).prodMk (PDSStochAux.pad_meas i))).sub
        (hf.meas_f.comp (measurable_const.prodMk (PDSStochAux.pad_meas i)))
    exact hbound_int _ hm ⟨|L| * R, fun ω =>
      le_trans (hlip _ (hXmem i ω) _) (habsL _ _ (norm_nonneg _) (hR ω))⟩
  have hfub : ∀ i ∈ range (k + 1), ∫ ω, ψ (X i ω) ∂P = ∫ ω, H i ω ∂P := by
    intro i hi
    have hik : i < k + 1 := mem_range.mp hi
    have hdep : ∀ ω ω' : ℕ → Ξ, (∀ j < ((⟨i, hik⟩ : Fin (k + 1)) : ℕ), ω j = ω' j) →
        ssaRun π γ x0 f' ω i = ssaRun π γ x0 f' ω' i := by
      intro ω ω' h
      simp only [ssaRun]
      rw [PDSStochAux.state_dep π γ x0 f' i ω ω' h]
    have hpad : ∀ ω : Fin (k + 1) → Ξ, padSample ω i = ω ⟨i, hik⟩ := fun ω => by
      simp [padSample, hik]
    have hH' : ∀ ω, H i ω = f (X i ω) (ω ⟨i, hik⟩) - f xstar (ω ⟨i, hik⟩) := fun ω => by
      simp only [H, hpad]
    have hint2 : Integrable (fun ω => f (X i ω) (ω ⟨i, hik⟩) - f xstar (ω ⟨i, hik⟩)) P :=
      (hH_int i).congr (Filter.Eventually.of_forall hH')
    have := PDSStochAux.fubini_step μ k ⟨i, hik⟩ (fun ω => ssaRun π γ x0 f' ω i) hdep
      (fun x ξ => f x ξ - f xstar ξ) (hψX_int i) hint2
    calc ∫ ω, ψ (X i ω) ∂P
        = ∫ ω, f (X i ω) (ω ⟨i, hik⟩) - f xstar (ω ⟨i, hik⟩) ∂P := this
      _ = ∫ ω, H i ω ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => (hH' ω).symm)
  have hconv : ConvexOn ℝ Q (expectedCost μ f) := by
    refine ⟨hd.convex, fun x hx y hy a b ha hb hab => ?_⟩
    have hmem : a • x + b • y ∈ Q := hd.convex hx hy ha hb hab
    simp only [expectedCost, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hf.integrable x hx).const_mul a) ((hf.integrable y hy).const_mul b)]
    refine integral_mono (hf.integrable _ hmem)
      (((hf.integrable x hx).const_mul a).add ((hf.integrable y hy).const_mul b)) fun ξ => ?_
    have := (hf.convex ξ).2 hx hy ha hb hab
    simpa [smul_eq_mul] using this
  have hw0 : 0 ≤ w := by positivity
  have hwsum : ∑ _i ∈ range (k + 1), w = 1 := by
    simp only [sum_const, card_range, nsmul_eq_mul, w]
    push_cast
    field_simp
  have hxbar_mem : ∀ ω, w • ∑ i ∈ range (k + 1), X i ω ∈ Q := by
    intro ω
    rw [smul_sum]
    exact hd.convex.sum_mem (fun i _ => hw0) hwsum (fun i _ => hXmem i ω)
  have hjensen : ∀ ω, ψ (w • ∑ i ∈ range (k + 1), X i ω) ≤ w * ∑ i ∈ range (k + 1), ψ (X i ω) := by
    intro ω
    have hJ := hconv.map_sum_le (t := range (k + 1)) (w := fun _ => w) (p := fun i => X i ω)
      (fun i _ => hw0) hwsum (fun i _ => hXmem i ω)
    simp only [smul_eq_mul] at hJ
    rw [hψφ _ (hxbar_mem ω), smul_sum, mul_sum]
    have e1 : ∑ i ∈ range (k + 1), w * ψ (X i ω)
        = ∑ i ∈ range (k + 1), w * expectedCost μ f (X i ω)
          - (∑ _i ∈ range (k + 1), w) * expectedCost μ f xstar := by
      rw [sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [hψφ _ (hXmem i ω)]; ring
    rw [e1, hwsum]
    linarith
  have hxbar_meas : Measurable (fun ω => w • ∑ i ∈ range (k + 1), X i ω) :=
    (Finset.measurable_sum _ fun i _ => hXmeas i).const_smul _
  have hsumψ_int : Integrable (fun ω => w * ∑ i ∈ range (k + 1), ψ (X i ω)) P :=
    (integrable_finset_sum _ fun i _ => hψX_int i).const_mul w
  have hψxbar_int : Integrable (fun ω => ψ (w • ∑ i ∈ range (k + 1), X i ω)) P := by
    refine Integrable.mono' hsumψ_int (hψmeas.comp hxbar_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψnn _ (hxbar_mem ω))]
    exact hjensen ω
  have step1 : ∫ ω, expectedCost μ f (w • ∑ i ∈ range (k + 1), X i ω) ∂P
      = ∫ ω, ψ (w • ∑ i ∈ range (k + 1), X i ω) ∂P + expectedCost μ f xstar := by
    have hpt : ∀ ω, expectedCost μ f (w • ∑ i ∈ range (k + 1), X i ω)
        = ψ (w • ∑ i ∈ range (k + 1), X i ω) + expectedCost μ f xstar := fun ω => by
      rw [hψφ _ (hxbar_mem ω)]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hψxbar_int (integrable_const _), integral_const, probReal_univ, one_smul]
  have step2 : ∫ ω, ψ (w • ∑ i ∈ range (k + 1), X i ω) ∂P
      ≤ w * ∑ i ∈ range (k + 1), ∫ ω, ψ (X i ω) ∂P := by
    rw [← integral_finset_sum _ (fun i _ => hψX_int i), ← integral_const_mul]
    exact integral_mono hψxbar_int hsumψ_int hjensen
  have step3 : ∑ i ∈ range (k + 1), ∫ ω, ψ (X i ω) ∂P ≤ C := by
    rw [sum_congr rfl hfub, ← integral_finset_sum _ (fun i _ => hH_int i)]
    have := integral_mono (integrable_finset_sum _ fun i _ => hH_int i) (integrable_const C)
      (fun ω => PDSStochAux.pathwise_loss hd hπ hγ f f' L hf.bound hf.subgrad (padSample ω) xstar hxstar k)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hC : betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) = w * C := by
    simp only [C, w]; ring
  rw [step1, hC]
  have := mul_le_mul_of_nonneg_left step3 hw0
  linarith
