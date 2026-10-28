-- Prove2me | solution 1 for RelaxedPRS.StrongCvx.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T01:51:08.162473+00:00
-- url     : https://prove2.me/submissions/d378f6af-ee57-44f3-a726-af5e812d06d1

import Mathlib
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

open Filter Topology Asymptotics

namespace E54

open scoped RealInnerProductSpace
open RelaxedPRS.StrongCvx ThreeOpSplitting.ConvexRates

theorem inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [inner_grad]
  exact this

theorem descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

theorem convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x y : E) : f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • w)) := by
    have := hf.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => f (x + t • w)) = f ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [inner_grad]
  linarith

/-- Half of the Baillon–Haddad inequality. -/
theorem bh_half {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {h : E → ℝ} {β : ℝ} (hβ : 0 < β) (hh : IsSmoothConvex β h) (x y : E) :
    h x + ⟪gradient h x, y - x⟫ + β / 2 * ‖gradient h y - gradient h x‖ ^ 2 ≤ h y := by
  set δ := gradient h y - gradient h x
  set w := y - β • δ
  have h1 := convex_fo hh.1 hh.2.1 x w
  have h2 := descent hh.2.1 hh.2.2 y w
  have ew1 : w - x = (y - x) - β • δ := by simp only [w]; abel
  have ew2 : w - y = -(β • δ) := by simp only [w]; abel
  rw [ew1, inner_sub_right, real_inner_smul_right] at h1
  rw [ew2, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hβ] at h2
  have hδ : ⟪gradient h y, δ⟫ - ⟪gradient h x, δ⟫ = ‖δ‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hb : β⁻¹ / 2 * (β * ‖δ‖) ^ 2 = β / 2 * ‖δ‖ ^ 2 := by
    field_simp
  rw [hb] at h2
  nlinarith

theorem cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {h : E → ℝ} {β : ℝ} (hβ : 0 < β) (hh : IsSmoothConvex β h) (x y : E) :
    β * ‖gradient h x - gradient h y‖ ^ 2 ≤ ⟪gradient h x - gradient h y, x - y⟫ := by
  have h1 := bh_half hβ hh x y
  have h2 := bh_half hβ hh y x
  have e1 : ‖gradient h x - gradient h y‖ = ‖gradient h y - gradient h x‖ := norm_sub_rev _ _
  have e2 : ⟪gradient h x - gradient h y, x - y⟫ =
      -⟪gradient h x, y - x⟫ - ⟪gradient h y, x - y⟫ := by
    rw [inner_sub_left, ← neg_sub x y, inner_neg_right]; ring
  rw [e1] at h2
  rw [e2, e1]
  linarith

/-- Gradient identification from a global affine minorant. -/
theorem grad_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {h : E → ℝ} {β : ℝ} (hβ : 0 < β) (hh : IsSmoothConvex β h) (p u : E)
    (hsub : ∀ z, h p + ⟪u, z - p⟫ ≤ h z) : gradient h p = u := by
  set δ := u - gradient h p
  have h1 := hsub (p + β • δ)
  have h2 := descent hh.2.1 hh.2.2 p (p + β • δ)
  rw [add_sub_cancel_left, real_inner_smul_right] at h1
  rw [add_sub_cancel_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hβ] at h2
  have hb : β⁻¹ / 2 * (β * ‖δ‖) ^ 2 = β / 2 * ‖δ‖ ^ 2 := by
    field_simp
  rw [hb] at h2
  have hδ : ⟪u, δ⟫ - ⟪gradient h p, δ⟫ = ‖δ‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have h3 : β * ‖δ‖ ^ 2 ≤ β / 2 * ‖δ‖ ^ 2 := by nlinarith
  have h4 : ‖δ‖ ^ 2 ≤ 0 := by nlinarith
  have h5 : ‖δ‖ = 0 := by nlinarith [norm_nonneg δ]
  have : δ = 0 := norm_eq_zero.mp h5
  exact (sub_eq_zero.mp this).symm

theorem prox_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} {γ : ℝ} {P : H → H} (hf : IsProperClosedConvex f)
    (hP : IsProx γ f P) (w : H) : ∃ a : ℝ, f (P w) = a := by
  obtain ⟨x0, hx0⟩ := hf.2.1
  have h := hP w x0
  have hne : f (P w) ≠ ⊤ := by
    intro htop
    rw [htop, ← EReal.coe_toReal hx0 (hf.1 x0), ← EReal.coe_add, EReal.top_add_coe] at h
    exact absurd h (not_le.mpr (EReal.coe_lt_top _))
  exact ⟨(f (P w)).toReal, (EReal.coe_toReal hne (hf.1 _)).symm⟩

/-- The strong prox inequality. -/
theorem prox_sc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} {γ μ : ℝ} {P : H → H} (hγ : 0 < γ) (hμ : 0 ≤ μ)
    (hsc : IsStrongCvxE μ f) (hP : IsProx γ f P) (w z : H) (a b : ℝ)
    (ha : f (P w) = a) (hb : f z = b) :
    a + ⟪w - P w, z - P w⟫ / γ + μ / 2 * ‖z - P w‖ ^ 2 ≤ b := by
  set p := P w with hp
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      a + ⟪w - p, z - p⟫ / γ + μ / 2 * ‖z - p‖ ^ 2 ≤
        b + t * ((μ / 2 + 1 / (2 * γ)) * ‖z - p‖ ^ 2) := by
    intro t ht0 ht1
    have hs := hsc z p t ht0.le ht1
    rw [ha, hb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hs
    have hpr := hP w (t • z + (1 - t) • p)
    rw [ha] at hpr
    have h2 := add_le_add hpr (le_refl (((μ / 2 * t * (1 - t) * ‖z - p‖ ^ 2 : ℝ)) : EReal))
    have h3 : f (t • z + (1 - t) • p) + ((‖t • z + (1 - t) • p - w‖ ^ 2 / (2 * γ) : ℝ) : EReal)
        + ((μ / 2 * t * (1 - t) * ‖z - p‖ ^ 2 : ℝ) : EReal) ≤
        ((t * b + (1 - t) * a : ℝ) : EReal)
          + ((‖t • z + (1 - t) • p - w‖ ^ 2 / (2 * γ) : ℝ) : EReal) := by
      rw [add_right_comm]
      exact add_le_add hs (le_refl _)
    have h4 := h2.trans h3
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h4
    have hvec : t • z + (1 - t) • p - w = (p - w) + t • (z - p) := by module
    rw [hvec, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0] at h4
    have hinner : ⟪w - p, z - p⟫ = -⟪p - w, z - p⟫ := by rw [← inner_neg_left, neg_sub]
    rw [hinner]
    have e : (‖p - w‖ ^ 2 + 2 * (t * ⟪p - w, z - p⟫) + (t * ‖z - p‖) ^ 2) / (2 * γ) =
        ‖p - w‖ ^ 2 / (2 * γ) + t * (⟪p - w, z - p⟫ / γ) + t * (t * ‖z - p‖ ^ 2 / (2 * γ)) := by
      field_simp
    rw [e, ← hp] at h4
    have h5 : t * (a + -⟪p - w, z - p⟫ / γ + μ / 2 * ‖z - p‖ ^ 2) ≤
        t * (b + t * ((μ / 2 + 1 / (2 * γ)) * ‖z - p‖ ^ 2)) := by
      have e2 : t * (t * ‖z - p‖ ^ 2 / (2 * γ)) = t * t * (1 / (2 * γ) * ‖z - p‖ ^ 2) := by ring
      rw [e2] at h4
      linear_combination h4
    exact le_of_mul_le_mul_left h5 ht0
  apply le_of_forall_pos_le_add
  intro ε hε
  have hC : 0 ≤ (μ / 2 + 1 / (2 * γ)) * ‖z - p‖ ^ 2 := by positivity
  set C := (μ / 2 + 1 / (2 * γ)) * ‖z - p‖ ^ 2
  obtain ⟨t, ht0, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t ≤ ε / (C + 1) :=
    ⟨min 1 (ε / (C + 1)), lt_min one_pos (by positivity), min_le_left _ _, min_le_right _ _⟩
  have h := key t ht0 ht1
  have h5 : t * (C + 1) ≤ ε := (le_div_iff₀ (by positivity)).mp ht2
  have h6 : t * C ≤ ε := by nlinarith
  linarith

/-- Strong monotonicity of the prox residuals. -/
theorem prox_mono {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} {γ μ : ℝ} {P : H → H} (hγ : 0 < γ) (hμ : 0 ≤ μ)
    (hf : IsProperClosedConvex f) (hsc : IsStrongCvxE μ f) (hP : IsProx γ f P) (w1 w2 : H) :
    μ * ‖P w1 - P w2‖ ^ 2 ≤ ⟪γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2), P w1 - P w2⟫ := by
  obtain ⟨a1, ha1⟩ := prox_fin hf hP w1
  obtain ⟨a2, ha2⟩ := prox_fin hf hP w2
  have h1 := prox_sc hγ hμ hsc hP w1 (P w2) a1 a2 ha1 ha2
  have h2 := prox_sc hγ hμ hsc hP w2 (P w1) a2 a1 ha2 ha1
  have e1 : ⟪γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2), P w1 - P w2⟫ =
      -(⟪w1 - P w1, P w2 - P w1⟫ / γ) - ⟪w2 - P w2, P w1 - P w2⟫ / γ := by
    rw [← smul_sub, real_inner_smul_left, inner_sub_left, ← neg_sub (P w2) (P w1),
      inner_neg_right]
    field_simp
  have e2 : ‖P w2 - P w1‖ = ‖P w1 - P w2‖ := norm_sub_rev _ _
  rw [e2] at h1
  rw [e1]
  linarith

/-- Firm nonexpansiveness consequence: reflections are nonexpansive. -/
theorem refl_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → EReal} {γ μ : ℝ} {P : H → H} (hγ : 0 < γ) (hμ : 0 ≤ μ)
    (hf : IsProperClosedConvex f) (hsc : IsStrongCvxE μ f) (hP : IsProx γ f P) (w1 w2 : H) :
    ‖RelaxedPRS.StrongCvx.refl P w1 - RelaxedPRS.StrongCvx.refl P w2‖ ≤ ‖w1 - w2‖ := by
  have hm := prox_mono hγ hμ hf hsc hP w1 w2
  have e1 : γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2) = γ⁻¹ • ((w1 - w2) - (P w1 - P w2)) := by
    module
  rw [e1, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hq : 0 ≤ μ * ‖P w1 - P w2‖ ^ 2 := by positivity
  have hg : 0 ≤ ⟪w1 - w2, P w1 - P w2⟫ - ‖P w1 - P w2‖ ^ 2 := by
    have h0 := hm.trans' hq
    have hγi : 0 < γ⁻¹ := inv_pos.mpr hγ
    by_contra hc
    replace hc := not_le.mp hc
    have : γ⁻¹ * (⟪w1 - w2, P w1 - P w2⟫ - ‖P w1 - P w2‖ ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hγi hc
    linarith
  have e2 : RelaxedPRS.StrongCvx.refl P w1 - RelaxedPRS.StrongCvx.refl P w2 =
      (2 : ℝ) • (P w1 - P w2) - (w1 - w2) := by
    simp only [RelaxedPRS.StrongCvx.refl]; module
  rw [e2]
  have hsq : ‖(2 : ℝ) • (P w1 - P w2) - (w1 - w2)‖ ^ 2 ≤ ‖w1 - w2‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_comm]
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq


theorem aux_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → EReal} {γ μ β : ℝ} {P : H → H} (hγ : 0 < γ) (hμ : 0 ≤ μ) (hβ : 0 ≤ β)
    (hf : IsProperClosedConvex f) (hsc : IsStrongCvxE μ f) (hP : IsProx γ f P)
    (hl : 0 < β → HasLipGrad β f) (w1 w2 y : H) (hy : P w2 = y) :
    2 * auxS μ β (P w1) y (γ⁻¹ • (w1 - P w1)) (γ⁻¹ • (w2 - P w2)) ≤
      ⟪γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2), P w1 - y⟫ := by
  subst hy
  have hm := prox_mono hγ hμ hf hsc hP w1 w2
  have hM0 : 0 ≤ ⟪γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2), P w1 - P w2⟫ :=
    le_trans (by positivity) hm
  have hcoc : β * ‖γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2)‖ ^ 2 ≤
      ⟪γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2), P w1 - P w2⟫ := by
    rcases hβ.lt_or_eq with hβp | hβ0
    · obtain ⟨h, hfh, hh⟩ := hl hβp
      have hsub : ∀ w z, h (P w) + ⟪γ⁻¹ • (w - P w), z - P w⟫ ≤ h z := by
        intro w z
        have h1 := prox_sc hγ hμ hsc hP w z (h (P w)) (h z) (hfh _) (hfh _)
        rw [real_inner_smul_left]
        have h2 : 0 ≤ μ / 2 * ‖z - P w‖ ^ 2 := by positivity
        have e : γ⁻¹ * ⟪w - P w, z - P w⟫ = ⟪w - P w, z - P w⟫ / γ := by ring
        linarith
      have g1 := grad_eq hβp hh (P w1) _ (hsub w1)
      have g2 := grad_eq hβp hh (P w2) _ (hsub w2)
      have := cocoercive hβp hh (P w1) (P w2)
      rw [g1, g2] at this
      exact this
    · subst hβ0; simpa using hM0
  unfold auxS
  rcases le_total (μ / 2 * ‖P w1 - P w2‖ ^ 2)
      (β / 2 * ‖γ⁻¹ • (w1 - P w1) - γ⁻¹ • (w2 - P w2)‖ ^ 2) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem fix_xf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Pf Pg : H → H) (zs : H) (h : TPRS Pf Pg zs = zs) :
    Pf (RelaxedPRS.StrongCvx.refl Pg zs) = xg Pg zs := by
  unfold TPRS RelaxedPRS.StrongCvx.refl at h
  have h2 : (2 : ℝ) • (Pf ((2 : ℝ) • Pg zs - zs) - Pg zs) = 0 := by
    have h3 := sub_eq_zero.mpr h
    rw [← h3]; module
  have := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  unfold RelaxedPRS.StrongCvx.refl xg
  exact sub_eq_zero.mp this

theorem alg_id {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a d e : H) (l : ℝ) :
    ‖a + (2 * l) • (e - d)‖ ^ 2 = ‖a‖ ^ 2 - 4 * l * (⟪(2 : ℝ) • d - a - e, e⟫ + ⟪a - d, d⟫)
      - l * (1 - l) * ‖(2 : ℝ) • (e - d)‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm a d, real_inner_comm a e, real_inner_comm d e]
  ring

theorem alg_two {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a d e : H) :
    ⟪(2 : ℝ) • d - a - e, e⟫ + ⟪a - d, d⟫ =
      -⟪a, (2 : ℝ) • (e - d)⟫ / 2 - ‖(2 : ℝ) • (e - d)‖ ^ 2 / 4 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm d e]
  ring

theorem jensen_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ℕ) (l : ℕ → ℝ) (v : ℕ → H)
    (hl : ∀ i ∈ s, 0 ≤ l i) (hs : 0 < ∑ i ∈ s, l i) :
    ‖(∑ i ∈ s, l i)⁻¹ • ∑ i ∈ s, l i • v i‖ ^ 2 ≤
      (∑ i ∈ s, l i)⁻¹ * ∑ i ∈ s, l i * ‖v i‖ ^ 2 := by
  have hc : ConvexOn ℝ Set.univ (fun x : H => ‖x‖ ^ 2) := by
    have := (convexOn_norm (E := H) convex_univ).pow (fun x _ => norm_nonneg x) 2
    exact this
  have hw0 : ∀ i ∈ s, 0 ≤ (∑ j ∈ s, l j)⁻¹ * l i :=
    fun i hi => mul_nonneg (inv_nonneg.mpr hs.le) (hl i hi)
  have hw1 : ∑ i ∈ s, (∑ j ∈ s, l j)⁻¹ * l i = 1 := by
    rw [← Finset.mul_sum]; exact inv_mul_cancel₀ hs.ne'
  have := hc.map_sum_le hw0 hw1 (fun i _ => Set.mem_univ (v i))
  simp only [smul_eq_mul] at this
  rw [Finset.smul_sum, Finset.mul_sum]
  simp only [smul_smul, mul_assoc] at this ⊢
  exact this

theorem erg_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam : ℕ → ℝ) (w : ℕ → H) (k : ℕ) (y : H) (hL : Lam lam k ≠ 0) :
    ergAvg lam w k - y = (Lam lam k)⁻¹ • ∑ i ∈ Finset.range (k + 1), lam i • (w i - y) := by
  have hL' : (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i = 1 := inv_mul_cancel₀ hL
  unfold ergAvg
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [smul_smul, hL', one_smul]

theorem erg_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ β : ℝ) (hμ : 0 ≤ μ) (hβ : 0 ≤ β) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (x u : ℕ → H) (y v : H) (k : ℕ) :
    auxS μ β (ergAvg lam x k) y (ergAvg lam u k) v ≤
      (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * auxS μ β (x i) y (u i) v := by
  have hL : 0 < Lam lam k := Finset.sum_pos (fun i _ => hlam i) Finset.nonempty_range_add_one
  have hl0 : ∀ i ∈ Finset.range (k + 1), 0 ≤ lam i := fun i _ => (hlam i).le
  have j1 : ‖ergAvg lam x k - y‖ ^ 2 ≤
      (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * ‖x i - y‖ ^ 2 := by
    rw [erg_sub lam x k y hL.ne']
    exact jensen_sq (Finset.range (k + 1)) lam (fun i => x i - y) hl0 hL
  have j2 : ‖ergAvg lam u k - v‖ ^ 2 ≤
      (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * ‖u i - v‖ ^ 2 := by
    rw [erg_sub lam u k v hL.ne']
    exact jensen_sq (Finset.range (k + 1)) lam (fun i => u i - v) hl0 hL
  have hLi : 0 ≤ (Lam lam k)⁻¹ := inv_nonneg.mpr hL.le
  unfold auxS
  apply max_le
  · calc μ / 2 * ‖ergAvg lam x k - y‖ ^ 2
        ≤ μ / 2 * ((Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * ‖x i - y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left j1 (by positivity)
      _ = (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * (μ / 2 * ‖x i - y‖ ^ 2) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (le_max_left _ _) (hlam i).le) hLi
  · calc β / 2 * ‖ergAvg lam u k - v‖ ^ 2
        ≤ β / 2 * ((Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * ‖u i - v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left j2 (by positivity)
      _ = (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * (β / 2 * ‖u i - v‖ ^ 2) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (le_max_right _ _) (hlam i).le) hLi

theorem best_littleO (a : ℕ → ℝ) (h0 : ∀ i, 0 ≤ a i) (hs : Summable a) :
    (fun k : ℕ => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one a) =o[atTop]
      (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have ht := tendsto_sum_nat_add a
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (c / 2) (half_pos hc)
  filter_upwards [eventually_ge_atTop (2 * N)] with k hk
  have hm0 : 0 ≤ (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one a :=
    Finset.le_inf' _ _ (fun i _ => h0 i)
  have hmle : ∀ i ∈ Finset.Ico (k / 2) (k + 1),
      (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one a ≤ a i := fun i hi =>
    Finset.inf'_le _ (Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
  have hcard := Finset.card_nsmul_le_sum (Finset.Ico (k / 2) (k + 1)) a _ hmle
  rw [Nat.card_Ico, nsmul_eq_mul] at hcard
  have hNk : N ≤ k / 2 := (Nat.le_div_iff_mul_le two_pos).mpr (by linarith)
  have hsum : Summable (fun j => a (j + k / 2)) := (summable_nat_add_iff (k / 2)).mpr hs
  have htail : ∑ i ∈ Finset.Ico (k / 2) (k + 1), a i ≤ ∑' j, a (j + k / 2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    calc ∑ j ∈ Finset.range (k + 1 - k / 2), a (k / 2 + j)
        = ∑ j ∈ Finset.range (k + 1 - k / 2), a (j + k / 2) := by
          simp only [add_comm]
      _ ≤ ∑' j, a (j + k / 2) := hsum.sum_le_tsum _ (fun j _ => h0 _)
  have hlt := hN (k / 2) hNk
  rw [Real.dist_eq, sub_zero] at hlt
  have htail' : ∑' j, a (j + k / 2) < c / 2 := lt_of_le_of_lt (le_abs_self _) hlt
  have hcast : ((k + 1 - k / 2 : ℕ) : ℝ) = (k : ℝ) + 1 - ((k / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : 2 * ((k / 2 : ℕ) : ℝ) ≤ k := by
    have := Nat.mul_div_le k 2
    have : ((2 * (k / 2) : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 * (k / 2) ≤ k)
    push_cast at this; linarith
  rw [hcast] at hcard
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hm0, Real.norm_eq_abs, abs_of_pos (by positivity),
    mul_one_div, le_div_iff₀ hk1]
  set m := (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one a
  set q : ℝ := ((k / 2 : ℕ) : ℝ)
  have hq : 0 ≤ ((k : ℝ) + 1 - 2 * q) * m := mul_nonneg (by linarith) hm0
  nlinarith

theorem inf_antitone (b : ℕ → ℝ) (hb : Antitone b) (k : ℕ) :
    (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one b = b k :=
  le_antisymm (Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_self k)))
    (Finset.le_inf' _ _ (fun i hi => hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))

theorem anti_littleO (b : ℕ → ℝ) (h0 : ∀ i, 0 ≤ b i) (hb : Antitone b) (hs : Summable b) :
    b =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) :=
  (best_littleO b h0 hs).congr_left (fun k => inf_antitone b hb k)

theorem sqrt_rate (S n : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hS0 : ∀ k, 0 ≤ S k)
    (hn0 : ∀ k, 0 ≤ n k) (hSn : ∀ k, S k ≤ C * n k)
    (hn : (fun k => n k ^ 2) =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1))) :
    S =o[atTop] (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1)) := by
  rw [Asymptotics.isLittleO_iff] at hn ⊢
  intro c hc
  have hε : 0 < c / (C + 1) := by positivity
  filter_upwards [hn (pow_pos hε 2)] with k hk
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hsq : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr hk1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_pos (by positivity), mul_one_div, le_div_iff₀ hk1] at hk
  have h1 : (n k * Real.sqrt ((k : ℝ) + 1)) ^ 2 ≤ (c / (C + 1)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hk1.le]; exact hk
  have h2 : n k * Real.sqrt ((k : ℝ) + 1) ≤ c / (C + 1) := by
    have := mul_nonneg (hn0 k) hsq.le
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (hS0 k), Real.norm_eq_abs, abs_of_pos (by positivity),
    mul_one_div, le_div_iff₀ hsq]
  have h3 : S k * Real.sqrt ((k : ℝ) + 1) ≤ C * (n k * Real.sqrt ((k : ℝ) + 1)) := by
    calc S k * Real.sqrt ((k : ℝ) + 1) ≤ (C * n k) * Real.sqrt ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (hSn k) hsq.le
      _ = C * (n k * Real.sqrt ((k : ℝ) + 1)) := by ring
  have h4 : C * (c / (C + 1)) ≤ c := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have h5 := mul_le_mul_of_nonneg_left h2 hC
  linarith

theorem telescope (x D : ℕ → ℝ) (h : ∀ k, x k ≤ D k - D (k + 1)) (hD : ∀ k, 0 ≤ D k)
    (N : ℕ) : ∑ i ∈ Finset.range N, x i ≤ D 0 := by
  have : ∀ N, ∑ i ∈ Finset.range N, x i ≤ D 0 - D N := by
    intro N
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [h n]
  linarith [this N, hD N]

theorem km_mono {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (w : H) (l : ℝ)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    ‖T ((1 - l) • w + l • T w) - ((1 - l) • w + l • T w)‖ ≤ ‖T w - w‖ := by
  have ev : T ((1 - l) • w + l • T w) - ((1 - l) • w + l • T w) =
      (T ((1 - l) • w + l • T w) - T w) + (1 - l) • (T w - w) := by module
  have ev2 : (1 - l) • w + l • T w - w = l • (T w - w) := by module
  calc ‖T ((1 - l) • w + l • T w) - ((1 - l) • w + l • T w)‖
      = ‖(T ((1 - l) • w + l • T w) - T w) + (1 - l) • (T w - w)‖ := by rw [ev]
    _ ≤ ‖T ((1 - l) • w + l • T w) - T w‖ + ‖(1 - l) • (T w - w)‖ := norm_add_le _ _
    _ ≤ ‖(1 - l) • w + l • T w - w‖ + (1 - l) * ‖T w - w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        gcongr
        exact hT _ _
    _ = ‖T w - w‖ := by
        rw [ev2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]; ring

noncomputable def MM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (Pf Pg : H → H) (w zs : H) : ℝ :=
  ⟪gtF γ Pf Pg w - gtF γ Pf Pg zs, xf Pf Pg w - xg Pg zs⟫ +
    ⟪gtG γ Pg w - gtG γ Pg zs, xg Pg w - xg Pg zs⟫

theorem perk {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H) (hPf : IsProx γ f Pf) (hPg : IsProx γ g Pg)
    (μf βf μg βg : ℝ) (hμf : 0 ≤ μf) (hβf : 0 ≤ βf) (hμg : 0 ≤ μg) (hβg : 0 ≤ βg)
    (hscf : IsStrongCvxE μf f) (hscg : IsStrongCvxE μg g)
    (hlf : 0 < βf → HasLipGrad βf f) (hlg : 0 < βg → HasLipGrad βg g)
    (zs : H) (hzs : TPRS Pf Pg zs = zs) (w : H) (l : ℝ) :
    (2 * auxS μf βf (xf Pf Pg w) (xg Pg zs) (gtF γ Pf Pg w) (gtF γ Pf Pg zs) +
      2 * auxS μg βg (xg Pg w) (xg Pg zs) (gtG γ Pg w) (gtG γ Pg zs) ≤ MM γ Pf Pg w zs) ∧
    ‖((1 - l) • w + l • TPRS Pf Pg w) - zs‖ ^ 2 = ‖w - zs‖ ^ 2 - 4 * γ * l * MM γ Pf Pg w zs
      - l * (1 - l) * ‖TPRS Pf Pg w - w‖ ^ 2 ∧
    γ * MM γ Pf Pg w zs ≤ ‖w - zs‖ * ‖TPRS Pf Pg w - w‖ / 2 := by
  have hfix : Pf (RelaxedPRS.StrongCvx.refl Pg zs) = xg Pg zs := fix_xf Pf Pg zs hzs
  have hA : 2 * auxS μf βf (xf Pf Pg w) (xg Pg zs) (gtF γ Pf Pg w) (gtF γ Pf Pg zs) ≤
      ⟪gtF γ Pf Pg w - gtF γ Pf Pg zs, xf Pf Pg w - xg Pg zs⟫ :=
    aux_bound hγ hμf hβf hf hscf hPf hlf (RelaxedPRS.StrongCvx.refl Pg w)
      (RelaxedPRS.StrongCvx.refl Pg zs) (xg Pg zs) hfix
  have hB : 2 * auxS μg βg (xg Pg w) (xg Pg zs) (gtG γ Pg w) (gtG γ Pg zs) ≤
      ⟪gtG γ Pg w - gtG γ Pg zs, xg Pg w - xg Pg zs⟫ :=
    aux_bound hγ hμg hβg hg hscg hPg hlg w zs (xg Pg zs) rfl
  have eT : TPRS Pf Pg w = (2 : ℝ) • xf Pf Pg w - ((2 : ℝ) • xg Pg w - w) := rfl
  have eFw : gtF γ Pf Pg w = γ⁻¹ • ((2 : ℝ) • xg Pg w - w - xf Pf Pg w) := rfl
  have eFs : gtF γ Pf Pg zs = γ⁻¹ • ((2 : ℝ) • xg Pg zs - zs - xg Pg zs) := by
    unfold gtF xf; rw [hfix]; rfl
  have eGw : gtG γ Pg w = γ⁻¹ • (w - xg Pg w) := rfl
  have eGs : gtG γ Pg zs = γ⁻¹ • (zs - xg Pg zs) := rfl
  have e1 : (1 - l) • w + l • TPRS Pf Pg w - zs = (w - zs) + (2 * l) •
      ((xf Pf Pg w - xg Pg zs) - (xg Pg w - xg Pg zs)) := by rw [eT]; module
  have e2 : gtF γ Pf Pg w - gtF γ Pf Pg zs = γ⁻¹ • ((2 : ℝ) • (xg Pg w - xg Pg zs)
      - (w - zs) - (xf Pf Pg w - xg Pg zs)) := by rw [eFw, eFs]; module
  have e3 : gtG γ Pg w - gtG γ Pg zs = γ⁻¹ • ((w - zs) - (xg Pg w - xg Pg zs)) := by
    rw [eGw, eGs]; module
  have e4 : TPRS Pf Pg w - w = (2 : ℝ) • ((xf Pf Pg w - xg Pg zs) - (xg Pg w - xg Pg zs)) := by
    rw [eT]; module
  have hγM : γ * MM γ Pf Pg w zs =
      ⟪(2 : ℝ) • (xg Pg w - xg Pg zs) - (w - zs) - (xf Pf Pg w - xg Pg zs),
        xf Pf Pg w - xg Pg zs⟫ + ⟪(w - zs) - (xg Pg w - xg Pg zs), xg Pg w - xg Pg zs⟫ := by
    unfold MM
    rw [e2, e3, real_inner_smul_left, real_inner_smul_left, ← mul_add, ← mul_assoc,
      mul_inv_cancel₀ hγ.ne', one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold MM; linarith
  · rw [e1, e4, alg_id]
    rw [show 4 * γ * l * MM γ Pf Pg w zs = 4 * l * (γ * MM γ Pf Pg w zs) by ring, hγM]
  · rw [hγM, alg_two, e4]
    have h1 := abs_real_inner_le_norm (w - zs)
      ((2 : ℝ) • ((xf Pf Pg w - xg Pg zs) - (xg Pg w - xg Pg zs)))
    have h2 := neg_abs_le (⟪w - zs,
      (2 : ℝ) • ((xf Pf Pg w - xg Pg zs) - (xg Pg w - xg Pg zs))⟫)
    have h3 := sq_nonneg ‖(2 : ℝ) • ((xf Pf Pg w - xg Pg zs) - (xg Pg w - xg Pg zs))‖
    linarith

theorem T_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : H → EReal) (hf : IsProperClosedConvex f) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H) (hPf : IsProx γ f Pf) (hPg : IsProx γ g Pg)
    (μf μg : ℝ) (hμf : 0 ≤ μf) (hμg : 0 ≤ μg)
    (hscf : IsStrongCvxE μf f) (hscg : IsStrongCvxE μg g) (x y : H) :
    ‖TPRS Pf Pg x - TPRS Pf Pg y‖ ≤ ‖x - y‖ :=
  (refl_nonexp hγ hμf hf hscf hPf _ _).trans (refl_nonexp hγ hμg hg hscg hPg _ _)


set_option maxHeartbeats 1000000 in
theorem main {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (μf βf μg βg : ℝ)
    (hμf : 0 ≤ μf) (hβf : 0 ≤ βf) (hμg : 0 ≤ μg) (hβg : 0 ≤ βg)
    (hscf : IsStrongCvxE μf f) (hscg : IsStrongCvxE μg g)
    (hlf : 0 < βf → HasLipGrad βf f)
    (hlg : 0 < βg → HasLipGrad βg g)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : TPRS Pf Pg zs = zs) :
    let xs := xg Pg zs
    let Sf : ℕ → ℝ := fun k =>
      auxS μf βf (xf Pf Pg (z k)) xs (gtF γ Pf Pg (z k)) (gtF γ Pf Pg zs)
    let Sg : ℕ → ℝ := fun k =>
      auxS μg βg (xg Pg (z k)) xs (gtG γ Pg (z k)) (gtG γ Pg zs)
    let SbarF : ℕ → ℝ := fun k =>
      auxS μf βf
        (ergAvg lam (fun i => xf Pf Pg (z i)) k) xs
        (ergAvg lam (fun i => gtF γ Pf Pg (z i)) k) (gtF γ Pf Pg zs)
    let SbarG : ℕ → ℝ := fun k =>
      auxS μg βg
        (ergAvg lam (fun i => xg Pg (z i)) k) xs
        (ergAvg lam (fun i => gtG γ Pg (z i)) k) (gtG γ Pg zs)
    (∀ k, 8 * γ * lam k * (Sf k + Sg k) ≤
      ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 +
        (1 - 1 / lam k) * ‖z (k + 1) - z k‖ ^ 2) ∧
    Summable (fun i => lam i * (Sf i + Sg i)) ∧
    8 * γ * (∑' i, lam i * (Sf i + Sg i)) ≤ ‖z 0 - zs‖ ^ 2 ∧
    ((∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ lam j) →
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sf) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sg) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1))) ∧
    (∀ k, SbarF k + SbarG k ≤
      ‖z 0 - zs‖ ^ 2 / (8 * γ * Lam lam k)) ∧
    ((∃ τ : ℝ, 0 < τ ∧ ∀ j, τ ≤ lam j * (1 - lam j)) →
      (fun k : ℕ => Sf k + Sg k) =o[Filter.atTop]
        (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1))) := by
  intro xs Sf Sg SbarF SbarG
  have hl0 : ∀ k, 0 < lam k := fun k => (hlam k).1
  have hl1 : ∀ k, lam k ≤ 1 := fun k => (hlam k).2
  have hP := fun k => perk f g hf hg γ hγ Pf Pg hPf hPg μf βf μg βg hμf hβf hμg hβg hscf hscg
    hlf hlg zs hzs (z k) (lam k)
  have hS2 : ∀ k, 2 * Sf k + 2 * Sg k ≤ MM γ Pf Pg (z k) zs := fun k => (hP k).1
  have hid : ∀ k, ‖z (k + 1) - zs‖ ^ 2 = ‖z k - zs‖ ^ 2 - 4 * γ * lam k * MM γ Pf Pg (z k) zs
      - lam k * (1 - lam k) * ‖TPRS Pf Pg (z k) - z k‖ ^ 2 := by
    intro k; rw [hz k]; exact (hP k).2.1
  have hF3 : ∀ k, γ * MM γ Pf Pg (z k) zs ≤ ‖z k - zs‖ * ‖TPRS Pf Pg (z k) - z k‖ / 2 :=
    fun k => (hP k).2.2
  have hSf0 : ∀ k, 0 ≤ Sf k := fun k => le_max_of_le_left (by positivity)
  have hSg0 : ∀ k, 0 ≤ Sg k := fun k => le_max_of_le_left (by positivity)
  have hM0 : ∀ k, 0 ≤ MM γ Pf Pg (z k) zs := fun k => by linarith [hS2 k, hSf0 k, hSg0 k]
  have h4 : ∀ k, (0 : ℝ) ≤ 4 * γ * lam k := fun k => by have := hl0 k; positivity
  have hstep : ∀ k, 8 * γ * lam k * (Sf k + Sg k) ≤ ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 := by
    intro k
    have h1 := mul_le_mul_of_nonneg_left (hS2 k) (h4 k)
    have h2 : 0 ≤ lam k * (1 - lam k) * ‖TPRS Pf Pg (z k) - z k‖ ^ 2 :=
      mul_nonneg (mul_nonneg (hl0 k).le (by linarith [hl1 k])) (sq_nonneg _)
    linarith [hid k]
  have hpart1 : ∀ k, 8 * γ * lam k * (Sf k + Sg k) ≤
      ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 + (1 - 1 / lam k) * ‖z (k + 1) - z k‖ ^ 2 := by
    intro k
    have ed : z (k + 1) - z k = lam k • (TPRS Pf Pg (z k) - z k) := by rw [hz k]; module
    have hne := (hl0 k).ne'
    have e : (1 - 1 / lam k) * ‖z (k + 1) - z k‖ ^ 2 =
        -(lam k * (1 - lam k) * ‖TPRS Pf Pg (z k) - z k‖ ^ 2) := by
      rw [ed, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; field_simp; ring
    have h1 := mul_le_mul_of_nonneg_left (hS2 k) (h4 k)
    rw [e]
    linarith [hid k]
  have hD : ∀ k, ‖z (k + 1) - zs‖ ^ 2 ≤ ‖z k - zs‖ ^ 2 := fun k => by
    have := hstep k
    have : 0 ≤ 8 * γ * lam k * (Sf k + Sg k) :=
      mul_nonneg (by linarith [h4 k]) (add_nonneg (hSf0 k) (hSg0 k))
    linarith
  have hDanti : Antitone (fun k => ‖z k - zs‖ ^ 2) := antitone_nat_of_succ_le hD
  have hDle : ∀ k, ‖z k - zs‖ ≤ ‖z 0 - zs‖ := fun k =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (hDanti (Nat.zero_le k))
  have hsumle : ∀ N, ∑ i ∈ Finset.range N, lam i * (Sf i + Sg i) ≤
      ‖z 0 - zs‖ ^ 2 / (8 * γ) := by
    intro N
    have ht := telescope (fun i => 8 * γ * (lam i * (Sf i + Sg i))) (fun k => ‖z k - zs‖ ^ 2)
      (fun k => by have := hstep k; show 8 * γ * (lam k * (Sf k + Sg k)) ≤ _ - _; linarith)
      (fun k => sq_nonneg _) N
    rw [← Finset.mul_sum] at ht
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hnn : ∀ i, 0 ≤ lam i * (Sf i + Sg i) :=
    fun i => mul_nonneg (hl0 i).le (add_nonneg (hSf0 i) (hSg0 i))
  have hsum : Summable (fun i => lam i * (Sf i + Sg i)) := summable_of_sum_range_le hnn hsumle
  have htsum : 8 * γ * (∑' i, lam i * (Sf i + Sg i)) ≤ ‖z 0 - zs‖ ^ 2 := by
    have := Real.tsum_le_of_sum_range_le hnn hsumle
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hbest : (∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ lam j) →
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sf) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sg) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    rintro ⟨c, hc, hcl⟩
    have hbd : ∀ i, c * (Sf i + Sg i) ≤ lam i * (Sf i + Sg i) := fun i =>
      mul_le_mul_of_nonneg_right (hcl i) (add_nonneg (hSf0 i) (hSg0 i))
    have hSfs : Summable Sf := Summable.of_nonneg_of_le hSf0
      (fun i => (show Sf i ≤ c⁻¹ * (lam i * (Sf i + Sg i)) by
        rw [inv_mul_eq_div, le_div_iff₀ hc]
        nlinarith [hbd i, mul_nonneg hc.le (hSg0 i)])) (hsum.mul_left c⁻¹)
    have hSgs : Summable Sg := Summable.of_nonneg_of_le hSg0
      (fun i => (show Sg i ≤ c⁻¹ * (lam i * (Sf i + Sg i)) by
        rw [inv_mul_eq_div, le_div_iff₀ hc]
        nlinarith [hbd i, mul_nonneg hc.le (hSf0 i)])) (hsum.mul_left c⁻¹)
    exact ⟨best_littleO Sf hSf0 hSfs, best_littleO Sg hSg0 hSgs⟩
  have herg : ∀ k, SbarF k + SbarG k ≤ ‖z 0 - zs‖ ^ 2 / (8 * γ * Lam lam k) := by
    intro k
    have hL : 0 < Lam lam k := Finset.sum_pos (fun i _ => hl0 i) Finset.nonempty_range_add_one
    have h1 : SbarF k ≤ (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * Sf i :=
      erg_aux μf βf hμf hβf lam hl0 (fun i => xf Pf Pg (z i)) (fun i => gtF γ Pf Pg (z i)) xs
        (gtF γ Pf Pg zs) k
    have h2 : SbarG k ≤ (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * Sg i :=
      erg_aux μg βg hμg hβg lam hl0 (fun i => xg Pg (z i)) (fun i => gtG γ Pg (z i)) xs
        (gtG γ Pg zs) k
    have h3 : ∑ i ∈ Finset.range (k + 1), lam i * Sf i + ∑ i ∈ Finset.range (k + 1), lam i * Sg i
        = ∑ i ∈ Finset.range (k + 1), lam i * (Sf i + Sg i) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    have h7 : (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * Sf i +
        (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * Sg i =
        (Lam lam k)⁻¹ * ∑ i ∈ Finset.range (k + 1), lam i * (Sf i + Sg i) := by
      rw [← mul_add, h3]
    have h6 := mul_le_mul_of_nonneg_left (hsumle (k + 1)) (inv_nonneg.mpr hL.le)
    have h5 : (Lam lam k)⁻¹ * (‖z 0 - zs‖ ^ 2 / (8 * γ)) =
        ‖z 0 - zs‖ ^ 2 / (8 * γ * Lam lam k) := by
      field_simp
    linarith
  have hlast : (∃ τ : ℝ, 0 < τ ∧ ∀ j, τ ≤ lam j * (1 - lam j)) →
      (fun k : ℕ => Sf k + Sg k) =o[Filter.atTop]
        (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1)) := by
    rintro ⟨τ, hτ, hτl⟩
    have hTn := T_nonexp f g hf hg γ hγ Pf Pg hPf hPg μf μg hμf hμg hscf hscg
    have hanti : Antitone (fun k => ‖TPRS Pf Pg (z k) - z k‖) := by
      apply antitone_nat_of_succ_le
      intro k
      show ‖TPRS Pf Pg (z (k + 1)) - z (k + 1)‖ ≤ ‖TPRS Pf Pg (z k) - z k‖
      rw [hz k]
      exact km_mono (TPRS Pf Pg) hTn (z k) (lam k) (hl0 k).le (hl1 k)
    have hstep2 : ∀ k, τ * ‖TPRS Pf Pg (z k) - z k‖ ^ 2 ≤
        ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 := by
      intro k
      have h1 := mul_le_mul_of_nonneg_right (hτl k) (sq_nonneg ‖TPRS Pf Pg (z k) - z k‖)
      have h2 : 0 ≤ 4 * γ * lam k * MM γ Pf Pg (z k) zs := mul_nonneg (h4 k) (hM0 k)
      linarith [hid k]
    have hb : ∀ N, ∑ i ∈ Finset.range N, ‖TPRS Pf Pg (z i) - z i‖ ^ 2 ≤ ‖z 0 - zs‖ ^ 2 / τ := by
      intro N
      have ht := telescope (fun i => τ * ‖TPRS Pf Pg (z i) - z i‖ ^ 2)
        (fun k => ‖z k - zs‖ ^ 2) hstep2 (fun k => sq_nonneg _) N
      rw [← Finset.mul_sum] at ht
      rw [le_div_iff₀ hτ]; linarith
    have hbs : Summable (fun i => ‖TPRS Pf Pg (z i) - z i‖ ^ 2) :=
      summable_of_sum_range_le (fun i => sq_nonneg _) hb
    have hbanti : Antitone (fun k => ‖TPRS Pf Pg (z k) - z k‖ ^ 2) := fun i j hij =>
      pow_le_pow_left₀ (norm_nonneg _) (hanti hij) 2
    have hbo := anti_littleO _ (fun i => sq_nonneg _) hbanti hbs
    have hC : 0 ≤ ‖z 0 - zs‖ / (4 * γ) := by positivity
    refine sqrt_rate (fun k => Sf k + Sg k) (fun k => ‖TPRS Pf Pg (z k) - z k‖)
      (‖z 0 - zs‖ / (4 * γ)) hC (fun k => add_nonneg (hSf0 k) (hSg0 k))
      (fun k => norm_nonneg _) ?_ hbo
    intro k
    show Sf k + Sg k ≤ ‖z 0 - zs‖ / (4 * γ) * ‖TPRS Pf Pg (z k) - z k‖
    have h1 := mul_le_mul_of_nonneg_left (hS2 k) hγ.le
    have h2 := hF3 k
    have h3 := mul_le_mul_of_nonneg_right (hDle k) (norm_nonneg (TPRS Pf Pg (z k) - z k))
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  exact ⟨hpart1, hsum, htsum, hbest, herg, hlast⟩

end E54

open RelaxedPRS.StrongCvx Filter Asymptotics in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (μf βf μg βg : ℝ)
    (hμf : 0 ≤ μf) (hβf : 0 ≤ βf) (hμg : 0 ≤ μg) (hβg : 0 ≤ βg)
    (hscf : IsStrongCvxE μf f) (hscg : IsStrongCvxE μg g)
    (hlf : 0 < βf → HasLipGrad βf f)
    (hlg : 0 < βg → HasLipGrad βg g)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : TPRS Pf Pg zs = zs) :
    let xs := xg Pg zs
    let Sf : ℕ → ℝ := fun k =>
      auxS μf βf (xf Pf Pg (z k)) xs (gtF γ Pf Pg (z k)) (gtF γ Pf Pg zs)
    let Sg : ℕ → ℝ := fun k =>
      auxS μg βg (xg Pg (z k)) xs (gtG γ Pg (z k)) (gtG γ Pg zs)
    let SbarF : ℕ → ℝ := fun k =>
      auxS μf βf
        (ergAvg lam (fun i => xf Pf Pg (z i)) k) xs
        (ergAvg lam (fun i => gtF γ Pf Pg (z i)) k) (gtF γ Pf Pg zs)
    let SbarG : ℕ → ℝ := fun k =>
      auxS μg βg
        (ergAvg lam (fun i => xg Pg (z i)) k) xs
        (ergAvg lam (fun i => gtG γ Pg (z i)) k) (gtG γ Pg zs)
    (∀ k, 8 * γ * lam k * (Sf k + Sg k) ≤
      ‖z k - zs‖ ^ 2 - ‖z (k + 1) - zs‖ ^ 2 +
        (1 - 1 / lam k) * ‖z (k + 1) - z k‖ ^ 2) ∧
    Summable (fun i => lam i * (Sf i + Sg i)) ∧
    8 * γ * (∑' i, lam i * (Sf i + Sg i)) ≤ ‖z 0 - zs‖ ^ 2 ∧
    ((∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ lam j) →
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sf) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
      (fun k : ℕ => (Finset.range (k + 1)).inf'
        (Finset.nonempty_range_add_one) Sg) =o[Filter.atTop]
          (fun k : ℕ => 1 / ((k : ℝ) + 1))) ∧
    (∀ k, SbarF k + SbarG k ≤
      ‖z 0 - zs‖ ^ 2 / (8 * γ * Lam lam k)) ∧
    ((∃ τ : ℝ, 0 < τ ∧ ∀ j, τ ≤ lam j * (1 - lam j)) →
      (fun k : ℕ => Sf k + Sg k) =o[Filter.atTop]
        (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 1))) := by
  exact E54.main f g hf hg γ hγ Pf Pg hPf hPg μf βf μg βg hμf hβf hμg hβg hscf hscg hlf hlg
    lam hlam z hz zs hzs
