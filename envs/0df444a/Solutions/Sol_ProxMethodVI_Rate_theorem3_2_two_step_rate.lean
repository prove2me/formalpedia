-- Prove2me | solution 1 for ProxMethodVI.Rate.theorem3_2_two_step_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T03:19:17.518593+00:00
-- url     : https://prove2.me/submissions/ff244811-8330-47e0-b55f-7f51ff904417

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

set_option autoImplicit false

namespace ProxMethodVI.Rate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lower bound of the Bregman distance from the monotone form of strong convexity. -/
lemma e6a_bregman_lb {Z : Set E} (hZc : Convex ℝ Z) {ω : E → ℝ} {ω' : E → E →L[ℝ] ℝ} {α : ℝ}
    (hω : IsStrongDGF Z ω ω' α) {x y : E} (hx : x ∈ Z) (hy : y ∈ Z) :
    α / 2 * ‖y - x‖ ^ 2 ≤ ω y - ω x - ω' x (y - x) := by
  set d := y - x with hd
  let p : ℝ → E := fun s => x + s • d
  have hmaps : Set.MapsTo p (Set.Icc 0 1) Z := fun s hs => hZc.add_smul_sub_mem hx hy hs
  let g : ℝ → ℝ := fun s => ω (p s) - ω x - s * ω' x d - α / 2 * s ^ 2 * ‖d‖ ^ 2
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt g
      (ω' (p s) d - ω' x d - α * s * ‖d‖ ^ 2) (Set.Icc 0 1) s := by
    intro s hs
    have hp : HasDerivWithinAt p d (Set.Icc 0 1) s := by
      have := ((hasDerivAt_id s).smul_const d).const_add x
      simpa [p] using this.hasDerivWithinAt
    have h1 : HasDerivWithinAt (ω ∘ p) (ω' (p s) d) (Set.Icc 0 1) s :=
      (hω.2.1 (p s) (hmaps hs)).comp_hasDerivWithinAt s hp hmaps
    have h2 : HasDerivAt (fun s : ℝ => s * ω' x d) (ω' x d) s := by
      simpa using (hasDerivAt_id s).mul_const (ω' x d)
    have h3 : HasDerivAt (fun s : ℝ => α / 2 * s ^ 2 * ‖d‖ ^ 2) (α * s * ‖d‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (α / 2)).mul_const (‖d‖ ^ 2)
      convert this using 1 <;> first | rfl | (push_cast; ring)
    have := ((h1.sub_const (ω x)).sub h2.hasDerivWithinAt).sub h3.hasDerivWithinAt
    exact this
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · intro s hs; exact (hderiv s hs).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs ⊢
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).mono Set.Ioo_subset_Icc_self
    · intro s hs
      rw [interior_Icc] at hs
      have hps : p s ∈ Z := hmaps (Set.Ioo_subset_Icc_self hs)
      have key := hω.2.2.2 (p s) hps x hx
      have hsub : p s - x = s • d := by simp [p]
      rw [hsub, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1] at key
      have hsp : 0 < s := hs.1
      have : α * s * ‖d‖ ^ 2 ≤ (ω' (p s) - ω' x) d := by
        have h' : s * (α * s * ‖d‖ ^ 2) ≤ s * (ω' (p s) - ω' x) d := by nlinarith
        exact le_of_mul_le_mul_left h' hsp
      simp only [ContinuousLinearMap.sub_apply] at this
      linarith
  have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [g, p] at h01
  simp at h01
  have hxd : x + d = y := by rw [hd]; abel
  rw [hxd] at h01
  linarith

/-- First-order optimality for a prox point. -/
lemma e6a_prox_foc {Z : Set E} (hZc : Convex ℝ Z) {ω : E → ℝ} {ω' : E → E →L[ℝ] ℝ} {α : ℝ}
    (hω : IsStrongDGF Z ω ω' α) {zc v : E} {ξ : E →L[ℝ] ℝ} (hv : IsProxPt Z ω ω' zc ξ v)
    {y : E} (hy : y ∈ Z) : 0 ≤ (ω' v + (ξ - ω' zc)) (y - v) := by
  have hf : HasFDerivWithinAt (fun y => ω y + (ξ - ω' zc) y) (ω' v + (ξ - ω' zc)) Z v :=
    (hω.2.1 v hv.1).add (ξ - ω' zc).hasFDerivWithinAt
  have hmin : IsLocalMinOn (fun y => ω y + (ξ - ω' zc) y) Z v :=
    IsMinOn.localize (fun y hy => hv.2 y hy)
  exact hmin.hasFDerivWithinAt_nonneg hf
    (sub_mem_posTangentConeAt_of_segment_subset (hZc.segment_subset hv.1 hy))

/-- One step: the key inequality `γ⟨F w, w - u⟩ ≤ V_{zc}(u) - V_{zn}(u)`. -/
lemma e6a_step_ineq {Z : Set E} (hZc : Convex ℝ Z) {ω : E → ℝ} {ω' : E → E →L[ℝ] ℝ} {α : ℝ}
    (hω : IsStrongDGF Z ω ω' α) {F : E → E →L[ℝ] ℝ} {γ : ℝ} {zc w zn : E}
    (hp : IsProxPt Z ω ω' zc (γ • F w) zn) (ht : test34 γ F ω ω' zc w zn) {u : E}
    (hu : u ∈ Z) :
    γ * F w (w - u) ≤ (ω u - ω zc - ω' zc (u - zc)) - (ω u - ω zn - ω' zn (u - zn)) := by
  have h := e6a_prox_foc hZc hω hp hu
  unfold test34 at ht
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub, mul_sub] at h ht ⊢
  linarith

/-- Claim 1, second branch: the corrector step meets (3.4) when `γ L ≤ α`. -/
lemma e6a_caseB_test {Z : Set E} (hZc : Convex ℝ Z) {ω : E → ℝ} {ω' : E → E →L[ℝ] ℝ} {α : ℝ}
    (hω : IsStrongDGF Z ω ω' α) {F : E → E →L[ℝ] ℝ} {L γ : ℝ} (hLip : IsLipschitzOnWRT Z F L)
    (hγ : 0 ≤ γ) (hγL : γ * L ≤ α) {zc w₁ zn : E} (hzc : zc ∈ Z)
    (hw₁ : IsProxPt Z ω ω' zc (γ • F zc) w₁) (hzn : IsProxPt Z ω ω' zc (γ • F w₁) zn) :
    test34 γ F ω ω' zc w₁ zn := by
  have hα : 0 < α := hω.1
  have hfoc := e6a_prox_foc hZc hω hw₁ hzn.1
  have B1 := e6a_bregman_lb hZc hω hzc hw₁.1
  have B2 := e6a_bregman_lb hZc hω hw₁.1 hzn.1
  have hL0 := hLip w₁ hw₁.1 zc hzc
  set a := ‖w₁ - zc‖ with ha
  set b := ‖w₁ - zn‖ with hb
  have hb' : ‖zn - w₁‖ = b := norm_sub_rev _ _
  rw [hb'] at B2
  have hlin : (F w₁ - F zc) (w₁ - zn) ≤ L * a * b := by
    calc (F w₁ - F zc) (w₁ - zn) ≤ ‖(F w₁ - F zc) (w₁ - zn)‖ := Real.le_norm_self _
      _ ≤ ‖F w₁ - F zc‖ * ‖w₁ - zn‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * a) * b := mul_le_mul_of_nonneg_right hL0 (norm_nonneg _)
  have hlin' : γ * ((F w₁ - F zc) (w₁ - zn)) ≤ γ * (L * a * b) :=
    mul_le_mul_of_nonneg_left hlin hγ
  have hab : 0 ≤ a * b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h1 : γ * (L * a * b) ≤ α * (a * b) := by
    have := mul_le_mul_of_nonneg_right hγL hab
    linarith [this]
  have h2 : α * (a * b) ≤ α / 2 * a ^ 2 + α / 2 * b ^ 2 := by
    nlinarith [mul_nonneg hα.le (sq_nonneg (a - b))]
  unfold test34
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub, mul_sub] at hfoc hlin' B1 B2 ⊢
  linarith

end ProxMethodVI.Rate

open ProxMethodVI.Rate in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (F : E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L) (hLip : IsLipschitzOnWRT Z F L)
    (hmono : IsMonotoneOnWRT Z F)
    (z w : ℕ → E) (hrun : IsBasicRun Z F ω ω' (α / (Real.sqrt 2 * L)) z w) :
    (∀ t : ℕ, test34 (α / (Real.sqrt 2 * L)) F ω ω' (z t) (w (t + 1)) (z (t + 1))) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ u ∈ Z,
        F u (((N : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 N, w t) - u)
          ≤ Real.sqrt 2 * theta Z ω ω' (z 0) * L / (α * N) := by
  have hα : 0 < α := hω.1
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := by linarith
  obtain ⟨hz0, hstep⟩ := hrun
  set γ := α / (Real.sqrt 2 * L) with hγdef
  have hγ : 0 < γ := by positivity
  have hγL : γ * L ≤ α := by
    have : γ * L = α / Real.sqrt 2 := by rw [hγdef]; field_simp
    rw [this]; exact div_le_self hα.le hs2
  have key : ∀ t, z t ∈ Z → z (t + 1) ∈ Z ∧ w (t + 1) ∈ Z ∧
      IsProxPt Z ω ω' (z t) (γ • F (w (t + 1))) (z (t + 1)) ∧
      test34 γ F ω ω' (z t) (w (t + 1)) (z (t + 1)) := by
    intro t hzt
    obtain ⟨w₁, hw₁, hA, hB⟩ := hstep t
    by_cases htest : test34 γ F ω ω' (z t) (z t) w₁
    · obtain ⟨hw, hz⟩ := hA htest
      rw [hw, hz]
      exact ⟨hw₁.1, hzt, hw₁, htest⟩
    · obtain ⟨hw, hz⟩ := hB htest
      rw [hw]
      exact ⟨hz.1, hw₁.1, hz, e6a_caseB_test hZc hω hLip hγ.le hγL hzt hw₁ hz⟩
  have hzmem : ∀ t, z t ∈ Z := by
    intro t
    induction t with
    | zero => exact hz0
    | succ n ih => exact (key n ih).1
  refine ⟨fun t => (key t (hzmem t)).2.2.2, ?_⟩
  intro N hN u hu
  have hsum : ∀ n : ℕ, γ * ∑ t ∈ Finset.Icc 1 n, F (w t) (w t - u) ≤
      (ω u - ω (z 0) - ω' (z 0) (u - z 0)) - (ω u - ω (z n) - ω' (z n) (u - z n)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add]
      have := e6a_step_ineq hZc hω (key n (hzmem n)).2.2.1 (key n (hzmem n)).2.2.2 hu
      linarith
  have hV : 0 ≤ ω u - ω (z N) - ω' (z N) (u - z N) := by
    have := e6a_bregman_lb hZc hω (hzmem N) hu
    have : 0 ≤ α / 2 * ‖u - z N‖ ^ 2 := by positivity
    linarith
  have hθ : ω u - ω (z 0) - ω' (z 0) (u - z 0) ≤ theta Z ω ω' (z 0) := by
    unfold theta
    refine le_csSup ?_ ⟨u, hu, rfl⟩
    apply hZk.bddAbove_image
    have hωc : ContinuousOn ω Z := fun p hp => (hω.2.1 p hp).continuousWithinAt
    exact (hωc.sub continuousOn_const).sub
      ((ω' (z 0)).continuous.comp (continuous_id.sub continuous_const)).continuousOn
  set X := ∑ t ∈ Finset.Icc 1 N, F (w t) (w t - u) with hXdef
  have hγX : γ * X ≤ theta Z ω ω' (z 0) := by linarith [hsum N]
  have hmon : ∑ t ∈ Finset.Icc 1 N, F u (w t - u) ≤ X := by
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    have hwk := (key k (hzmem k)).2.1
    have := hmono (w (k + 1)) hwk u hu
    simp only [ContinuousLinearMap.sub_apply] at this
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hrw : F u (((N : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 N, w t) - u) =
      (N : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 N, F u (w t - u) := by
    simp only [map_sub, map_smul, map_sum, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    field_simp
  have hX : X ≤ Real.sqrt 2 * L / α * theta Z ω ω' (z 0) := by
    have hc : 0 ≤ Real.sqrt 2 * L / α := by positivity
    calc X = Real.sqrt 2 * L / α * (γ * X) := by rw [hγdef]; field_simp
      _ ≤ Real.sqrt 2 * L / α * theta Z ω ω' (z 0) := mul_le_mul_of_nonneg_left hγX hc
  rw [hrw]
  calc (N : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 N, F u (w t - u)
      ≤ (N : ℝ)⁻¹ * X := mul_le_mul_of_nonneg_left hmon (by positivity)
    _ ≤ (N : ℝ)⁻¹ * (Real.sqrt 2 * L / α * theta Z ω ω' (z 0)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = Real.sqrt 2 * theta Z ω ω' (z 0) * L / (α * N) := by field_simp
