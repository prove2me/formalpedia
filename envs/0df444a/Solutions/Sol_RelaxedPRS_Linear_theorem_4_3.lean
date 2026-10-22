-- Prove2me | solution 1 for RelaxedPRS.Linear.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T18:54:03.209992+00:00
-- url     : https://prove2.me/submissions/23766413-5769-4c79-8267-9febba86ff5e

import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

set_option autoImplicit false
open scoped InnerProductSpace
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization RelaxedPRS.StrongCvx

theorem rpl_limit_aux (a b c e : ℝ) (he : 0 ≤ e)
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → a ≤ b + c + s * e) : a ≤ b + c := by
  by_contra hcon
  push_neg at hcon
  set δ := a - b - c with hδ
  have hδpos : 0 < δ := by linarith
  have hpos : 0 < δ / (2 * (e + 1)) := by positivity
  set s := min 1 (δ / (2 * (e + 1))) with hs
  have hs0 : 0 < s := lt_min one_pos hpos
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ δ / (2 * (e + 1)) := min_le_right _ _
  have := h s hs0 hs1
  have h3 : s * e ≤ δ / (2 * (e + 1)) * e := mul_le_mul_of_nonneg_right hs2 he
  have h4 : δ / (2 * (e + 1)) * e ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem rpl_prox_subgrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : IsProperClosedConvex f) (γ : ℝ) (hγ : 0 < γ) (P : H → H)
    (hP : IsProx γ f P) (z : H) : γ⁻¹ • (z - P z) ∈ subgrad f (P z) := by
  obtain ⟨hbot, ⟨y0, hy0⟩, -, hconv⟩ := hf
  set p := P z with hp
  have hpbot := hbot p
  have hptop : f p ≠ ⊤ := by
    intro h
    have h1 := hP z y0
    rw [← hp, h] at h1
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f y0 = r := ⟨(f y0).toReal, (EReal.coe_toReal hy0 (hbot y0)).symm⟩
    rw [hr, ← EReal.coe_add, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), top_le_iff] at h1
    exact EReal.coe_ne_top _ h1
  refine ⟨hpbot, hptop, fun u => ?_⟩
  by_cases hu : f u = ⊤
  · rw [hu]; exact le_top
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f p = a := ⟨(f p).toReal, (EReal.coe_toReal hptop hpbot).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f u = b := ⟨(f u).toReal, (EReal.coe_toReal hu (hbot u)).symm⟩
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      a ≤ b + γ⁻¹ * ⟪p - z, u - p⟫_ℝ + s * (‖u - p‖ ^ 2 / (2 * γ)) := by
    intro s hs0 hs1
    have hmem : ((1 - s) • p + s • u, (1 - s) * a + s * b) ∈
        {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} := by
      have := hconv (show (p, a) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} by
          simp only [Set.mem_setOf_eq]; rw [ha])
        (show (u, b) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} by
          simp only [Set.mem_setOf_eq]; rw [hb]) (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
      simpa using this
    simp only [Set.mem_setOf_eq] at hmem
    have h1 := hP z ((1 - s) • p + s • u)
    rw [← hp, ha] at h1
    have h2 : f ((1 - s) • p + s • u) + (((‖(1 - s) • p + s • u - z‖ ^ 2 / (2 * γ) : ℝ)) : EReal) ≤
        (((1 - s) * a + s * b : ℝ) : EReal) + (((‖(1 - s) • p + s • u - z‖ ^ 2 / (2 * γ) : ℝ)) : EReal) :=
      add_le_add hmem le_rfl
    have h3 := h1.trans h2
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have hy : (1 - s) • p + s • u - z = (p - z) + s • (u - p) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [hy] at h3
    have hn : ‖(p - z) + s • (u - p)‖ ^ 2 =
        ‖p - z‖ ^ 2 + 2 * s * ⟪p - z, u - p⟫_ℝ + s ^ 2 * ‖u - p‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hs0.le]
      ring
    rw [hn] at h3
    -- h3 : a + ‖p-z‖^2/(2γ) ≤ (1-s) a + s b + (…)/(2γ)
    have h4 : s * a ≤ s * (b + γ⁻¹ * ⟪p - z, u - p⟫_ℝ + s * (‖u - p‖ ^ 2 / (2 * γ))) := by
      have e1 : (‖p - z‖ ^ 2 + 2 * s * ⟪p - z, u - p⟫_ℝ + s ^ 2 * ‖u - p‖ ^ 2) / (2 * γ) =
          ‖p - z‖ ^ 2 / (2 * γ) + s * (γ⁻¹ * ⟪p - z, u - p⟫_ℝ) +
            s ^ 2 * (‖u - p‖ ^ 2 / (2 * γ)) := by
        field_simp
      rw [e1] at h3
      nlinarith
    exact le_of_mul_le_mul_left h4 hs0
  have := rpl_limit_aux a b (γ⁻¹ * ⟪p - z, u - p⟫_ℝ) (‖u - p‖ ^ 2 / (2 * γ)) (by positivity) key
  have e3 : ⟪u - p, γ⁻¹ • (z - p)⟫_ℝ = -(γ⁻¹ * ⟪p - z, u - p⟫_ℝ) := by
    rw [inner_smul_right]
    have : ⟪p - z, u - p⟫_ℝ = -⟪z - p, u - p⟫_ℝ := by rw [← inner_neg_left, neg_sub]
    rw [this, real_inner_comm]
    ring
  show a + ⟪u - p, γ⁻¹ • (z - P z)⟫_ℝ ≤ b
  rw [← hp, e3]
  linarith

theorem accepted_prs_identities {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg) (t : ℝ) (ht : 0 < t) (z : H) :
    RelaxedPRS.StrongCvx.gtG γ Pg z ∈ MoreauProx.Characterization.subgrad g (RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∈ MoreauProx.Characterization.subgrad f (RelaxedPRS.StrongCvx.xf Pf Pg z) ∧
    RelaxedPRS.StrongCvx.xg Pg z = z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z ∧
    RelaxedPRS.StrongCvx.xf Pf Pg z = RelaxedPRS.StrongCvx.xg Pg z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z - γ • RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = (2 * t) • (RelaxedPRS.StrongCvx.xf Pf Pg z - RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = -(2 * t * γ) • (RelaxedPRS.StrongCvx.gtG γ Pg z + RelaxedPRS.StrongCvx.gtF γ Pf Pg z) := by
  have hγ' : γ ≠ 0 := hγ.ne'
  have e1 : γ • (γ⁻¹ • (z - Pg z)) = z - Pg z := by rw [smul_smul, mul_inv_cancel₀ hγ', one_smul]
  have e2 : γ • (γ⁻¹ • (RelaxedPRS.StrongCvx.refl Pg z - Pf (RelaxedPRS.StrongCvx.refl Pg z))) = RelaxedPRS.StrongCvx.refl Pg z - Pf (RelaxedPRS.StrongCvx.refl Pg z) := by
    rw [smul_smul, mul_inv_cancel₀ hγ', one_smul]
  refine ⟨rpl_prox_subgrad g hg γ hγ Pg hPg z, rpl_prox_subgrad f hf γ hγ Pf hPf (RelaxedPRS.StrongCvx.refl Pg z), ?_, ?_, ?_, ?_⟩
  · simp only [gtG, xg, e1]; abel
  · simp only [gtG, gtF, xg, xf, RelaxedPRS.StrongCvx.refl]
    match_scalars <;> field_simp <;> ring
  · simp only [Tlam, TPRS, xf, xg, RelaxedPRS.StrongCvx.refl]; module
  · simp only [Tlam, TPRS, gtG, gtF, xf, xg, RelaxedPRS.StrongCvx.refl]
    match_scalars <;> field_simp <;> ring


set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem sgd36_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem sgd36_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := sgd36_line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ = ⟪G (x + c • w) - G x, w⟫ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
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

open scoped RealInnerProductSpace in
theorem sgd36_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫ ≤ F y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => F (x + t • w)) := by
    have := hc.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => F (x + t • w)) = F ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using sgd36_line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

-- Co-coercivity: ‖G y - G x‖² ≤ 2L (F y - F x - ⟪G x, y - x⟫).
open scoped RealInnerProductSpace in
theorem sgd36_cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (hc : ConvexOn ℝ Set.univ F) (x y : E) :
    ‖G y - G x‖ ^ 2 ≤ 2 * L * (F y - F x - ⟪G x, y - x⟫) := by
  -- φ z = F z - ⟪G x, z⟫, gradient H z = G z - G x
  set φ : E → ℝ := fun z => F z - ⟪G x, z⟫ with hφdef
  set H : E → E := fun z => G z - G x with hHdef
  have hφ : ∀ z, HasGradientAt φ (H z) z := by
    intro z
    have h1 := hasGradientAt_iff_hasFDerivAt.mp (hF z)
    have h2 : HasFDerivAt (fun z : E => ⟪G x, z⟫) (InnerProductSpace.toDual ℝ E (G x)) z := by
      have e : (fun z : E => ⟪G x, z⟫) = ⇑(InnerProductSpace.toDual ℝ E (G x)) := by
        funext z; simp [InnerProductSpace.toDual_apply_apply]
      rw [e]; exact ContinuousLinearMap.hasFDerivAt _
    rw [hasGradientAt_iff_hasFDerivAt, map_sub]
    exact h1.sub h2
  have hH : ∀ a b, ‖H a - H b‖ ≤ L * ‖a - b‖ := by
    intro a b; simp only [hHdef, sub_sub_sub_cancel_right]; exact hG a b
  -- φ minimized at x
  have hmin : ∀ z, φ x ≤ φ z := by
    intro z
    have := sgd36_convex_fo hF hc x z
    simp only [hφdef, inner_sub_right] at this ⊢
    linarith
  set v := H y
  have hd := sgd36_descent hφ hH y (y - (1 / L) • v)
  have hm := hmin (y - (1 / L) • v)
  have e1 : y - (1 / L) • v - y = -((1 / L) • v) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / L), real_inner_self_eq_norm_sq] at hd
  have key : ‖v‖ ^ 2 ≤ 2 * L * (φ y - φ x) := by
    have hL' : L ≠ 0 := hL.ne'
    have : φ x ≤ φ y - 1 / (2 * L) * ‖v‖ ^ 2 := by
      have h := hm.trans hd
      have : -(1 / L * ‖v‖ ^ 2) + L / 2 * (1 / L * ‖v‖) ^ 2 = - (1 / (2 * L) * ‖v‖ ^ 2) := by
        field_simp; ring
      linarith
    have h2 : 2 * L * (1 / (2 * L) * ‖v‖ ^ 2) = ‖v‖ ^ 2 := by field_simp
    nlinarith
  have hv : v = G y - G x := rfl
  rw [← hv]
  have : φ y - φ x = F y - F x - ⟪G x, y - x⟫ := by
    simp only [hφdef, inner_sub_right]; ring
  rw [← this]; exact key

open scoped InnerProductSpace RealInnerProductSpace in
theorem sgd36_main {n : ℕ} (f : ConvexOptAlg.StrongGD.E n → ℝ)
    (g : ConvexOptAlg.StrongGD.E n → ConvexOptAlg.StrongGD.E n) (β : ℝ)
    (hβ : 0 < β) (hsm : ConvexOptAlg.StrongGD.IsBetaSmooth f g β)
    (hcvx : ConvexOn ℝ (Set.univ : Set (ConvexOptAlg.StrongGD.E n)) f)
    (x y : ConvexOptAlg.StrongGD.E n) :
    (1 / β) * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := by
  obtain ⟨hF, -, hG⟩ := hsm
  have h1 := sgd36_cocoercive hβ hF hG hcvx x y
  have h2 := sgd36_cocoercive hβ hF hG hcvx y x
  have e1 : ‖g y - g x‖ = ‖g x - g y‖ := norm_sub_rev _ _
  rw [e1] at h1
  have e2 : ⟪g x - g y, x - y⟫_ℝ = -⟪g x, y - x⟫_ℝ - ⟪g y, x - y⟫_ℝ := by
    have : y - x = -(x - y) := by abel
    rw [this, inner_neg_right, inner_sub_left]; ring
  rw [e2]
  have key : ‖g x - g y‖ ^ 2 ≤ β * (-⟪g x, y - x⟫_ℝ - ⟪g y, x - y⟫_ℝ) := by nlinarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hβ]
  linarith


open ConvexOptAlg.StrongGD InnerProductSpace in
theorem accepted_cocoercivity {n : ℕ} (hn : 0 < n) (f : E n → ℝ) (g : E n → E n) (β : ℝ)
    (hβ : 0 < β) (hsm : IsBetaSmooth f g β)
    (hcvx : ConvexOn ℝ (Set.univ : Set (E n)) f) :
    ∀ x y : E n,
      (1 / β) * ‖g x - g y‖ ^ 2 ≤ ⟪g x - g y, x - y⟫_ℝ := by
  intro x y
  exact sgd36_main f g β hβ hsm hcvx x y

open scoped InnerProductSpace
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization RelaxedPRS.StrongCvx

namespace QueeliusPRS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem subgrad_gradient (h : H → ℝ) (hd : Differentiable ℝ h) (x u : H)
    (hu : u ∈ subgrad (fun y => (h y : EReal)) x) : u = gradient h x := by
  have hm : IsLocalMin (fun y => h y - ⟪u,y⟫_ℝ) x := by
    apply Filter.Eventually.of_forall
    intro y
    have hy := hu.2.2 y
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hy
    rw [real_inner_comm, inner_sub_right] at hy
    linarith
  have hd' := (hd x).hasGradientAt.hasFDerivAt.sub (innerSL ℝ u).hasFDerivAt
  have hz := congrArg (fun L : H →L[ℝ] ℝ => L (gradient h x-u))
    (hd'.fderiv.symm.trans hm.fderiv_eq_zero)
  simp only [ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply, ContinuousLinearMap.zero_apply] at hz
  have hzero : gradient h x-u=0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by
    simpa only [inner_sub_left] using hz)
  exact (sub_eq_zero.mp hzero).symm

theorem prox_gradient (g : H → EReal) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (P : H → H) (hP : IsProx γ g P)
    (h : H → ℝ) (hgh : ∀ x, g x = (h x : EReal))
    (hd : Differentiable ℝ h) (z : H) : z = P z + γ • gradient h (P z) := by
  have heq : g = fun x => (h x : EReal) := funext hgh
  have hs := rpl_prox_subgrad g hg γ hγ P hP z
  rw [heq] at hs
  have hh := subgrad_gradient h hd (P z) (γ⁻¹ • (z-P z)) hs
  rw [← hh,smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]
  abel

theorem norm_three (a b c : H) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have ht := (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) (le_refl ‖c‖))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖a‖+‖b‖+‖c‖)).2 ht
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

theorem strong_subgradient (f : H → EReal) (μ : ℝ) (hμ : 0 ≤ μ)
    (hsc : IsStrongCvxE μ f) (x y u : H)
    (hu : u ∈ subgrad f x) (hybot : f y ≠ ⊥) (hytop : f y ≠ ⊤) :
    (f x).toReal + ⟪y-x,u⟫_ℝ + μ/2*‖y-x‖^2 ≤ (f y).toReal := by
  let a := (f x).toReal
  let b := (f y).toReal
  have hx : f x = (a : EReal) := (EReal.coe_toReal hu.2.1 hu.1).symm
  have hy : f y = (b : EReal) := (EReal.coe_toReal hytop hybot).symm
  let q := μ/2*‖y-x‖^2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      a + ⟪y-x,u⟫_ℝ + q ≤ b + 0 + t*q := by
    intro t ht ht1
    have h1 := hsc y x t ht.le ht1
    have h2 := add_le_add (hu.2.2 (t • y + (1-t) • x))
      (le_refl (((μ/2*t*(1-t)*‖y-x‖^2 : ℝ)) : EReal))
    have h3 := h2.trans h1
    rw [hx,hy,← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,
      ← EReal.coe_add,← EReal.coe_add,EReal.coe_le_coe_iff] at h3
    have hm : t • y+(1-t) • x-x = t • (y-x) := by module
    rw [hm,real_inner_smul_left] at h3
    have hscaled : t*(a+⟪y-x,u⟫_ℝ+q) ≤ t*(b+t*q) := by
      dsimp [q] at *
      nlinarith only [h3]
    simpa using le_of_mul_le_mul_left hscaled ht
  simpa only [add_zero] using rpl_limit_aux (a+⟪y-x,u⟫_ℝ+q) b 0 q hq key

theorem strong_monotone (f : H → EReal) (μ : ℝ) (hμ : 0 ≤ μ)
    (hsc : IsStrongCvxE μ f) (x y u v : H)
    (hu : u ∈ subgrad f x) (hv : v ∈ subgrad f y) :
    μ*‖x-y‖^2 ≤ ⟪x-y,u-v⟫_ℝ := by
  have h1 := strong_subgradient f μ hμ hsc x y u hu hv.1 hv.2.1
  have h2 := strong_subgradient f μ hμ hsc y x v hv hu.1 hu.2.1
  rw [norm_sub_rev y x] at h1
  have he : ⟪y-x,u⟫_ℝ = -⟪x-y,u⟫_ℝ := by rw [← inner_neg_left,neg_sub]
  rw [he] at h1
  rw [inner_sub_right]
  linarith

theorem smooth_monotone (h : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hh : IsSmoothConvex β h) (x y : H) :
    β*‖gradient h x-gradient h y‖^2 ≤ ⟪x-y,gradient h x-gradient h y⟫_ℝ := by
  have h1 := sgd36_cocoercive (inv_pos.mpr hβ) (fun x => (hh.2.1 x).hasGradientAt) hh.2.2 hh.1 x y
  have h2 := sgd36_cocoercive (inv_pos.mpr hβ) (fun x => (hh.2.1 x).hasGradientAt) hh.2.2 hh.1 y x
  rw [norm_sub_rev] at h1
  have he : ⟪gradient h x,y-x⟫_ℝ = -⟪gradient h x,x-y⟫_ℝ := by rw [← inner_neg_right,neg_sub]
  rw [he] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hβ.le
  have h4 := mul_le_mul_of_nonneg_left h2 hβ.le
  have hb : β*2*β⁻¹=2 := by field_simp
  simp only [← mul_assoc,hb] at h3 h4
  rw [inner_sub_right]
  have hc1 : ⟪x-y,gradient h x⟫_ℝ = ⟪gradient h x,x-y⟫_ℝ := real_inner_comm _ _
  have hc2 : ⟪x-y,gradient h y⟫_ℝ = ⟪gradient h y,x-y⟫_ℝ := real_inner_comm _ _
  rw [hc1,hc2]
  nlinarith only [h3,h4]

theorem energy (a b v : H) (γ t : ℝ) (hγ : γ ≠ 0) :
    ‖b+γ • v‖^2-‖b+γ • v+(2*t) • (a-b)‖^2 =
      4*γ*t*⟪a,γ⁻¹ • (b-a)-v⟫_ℝ + 4*γ*t*⟪b,v⟫_ℝ +
      4*t*(1-t)*‖a-b‖^2 := by
  simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
    inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  have hba : ⟪b,a⟫_ℝ = ⟪a,b⟫_ℝ := real_inner_comm _ _
  have hva : ⟪v,a⟫_ℝ = ⟪a,v⟫_ℝ := real_inner_comm _ _
  have hvb : ⟪v,b⟫_ℝ = ⟪b,v⟫_ℝ := real_inner_comm _ _
  rw [hba,hva,hvb]
  field_simp
  <;> ring

theorem fixed_aux (Pf Pg : H → H) (zs : H) (hzs : TPRS Pf Pg zs=zs) :
    xf Pf Pg zs=xg Pg zs := by
  have he : (2 : ℝ) • (xf Pf Pg zs-xg Pg zs)=0 := by
    calc
      _ = TPRS Pf Pg zs-zs := by dsimp [TPRS,RelaxedPRS.StrongCvx.refl,xf,xg]; module
      _ = 0 := by rw [hzs,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left (by norm_num))

theorem step_energy (Pf Pg : H → H) (z zs : H) (γ t : ℝ) (hγ : γ ≠ 0)
    (hzs : TPRS Pf Pg zs=zs) :
    ‖z-zs‖^2-‖Tlam Pf Pg t z-zs‖^2 =
      4*γ*t*⟪xf Pf Pg z-xg Pg zs,gtF γ Pf Pg z-gtF γ Pf Pg zs⟫_ℝ +
      4*γ*t*⟪xg Pg z-xg Pg zs,gtG γ Pg z-gtG γ Pg zs⟫_ℝ +
      4*t*(1-t)*‖xf Pf Pg z-xg Pg z‖^2 := by
  let a := xf Pf Pg z-xg Pg zs
  let b := xg Pg z-xg Pg zs
  let v := gtG γ Pg z-gtG γ Pg zs
  have hs := fixed_aux Pf Pg zs hzs
  have hd : z-zs=b+γ • v := by
    dsimp [b,v,gtG,xg]
    simp only [smul_sub,smul_smul,mul_inv_cancel₀ hγ,one_smul]
    module
  have hu : gtF γ Pf Pg z-gtF γ Pf Pg zs=γ⁻¹ • (b-a)-v := by
    dsimp [a,b,v,gtF]
    rw [hs]
    dsimp [gtG,RelaxedPRS.StrongCvx.refl,xg,xf]
    module
  have hn : Tlam Pf Pg t z-zs=b+γ • v+(2*t) • (a-b) := by
    rw [← hd]
    dsimp [a,b,Tlam,TPRS,RelaxedPRS.StrongCvx.refl,xf,xg]
    module
  have hab : a-b=xf Pf Pg z-xg Pg z := by dsimp [a,b]; module
  rw [hd,hn,energy a b v γ t hγ,← hu,hab]

theorem regularity_bound (f : H → EReal) (μ β : ℝ) (hμ : 0 ≤ μ) (hβ : 0 ≤ β)
    (hsc : IsStrongCvxE μ f) (hl : 0 < β → HasLipGrad β f)
    (x y u v : H) (hu : u ∈ subgrad f x) (hv : v ∈ subgrad f y) :
    2*auxS μ β x y u v ≤ ⟪x-y,u-v⟫_ℝ := by
  have hstrong := strong_monotone f μ hμ hsc x y u v hu hv
  have hsmooth : β*‖u-v‖^2 ≤ ⟪x-y,u-v⟫_ℝ := by
    by_cases hpos : 0 < β
    · obtain ⟨h,hhf,hh⟩ := hl hpos
      have he : f=fun x => (h x : EReal) := funext hhf
      rw [he] at hu hv
      rw [subgrad_gradient h hh.2.1 x u hu,subgrad_gradient h hh.2.1 y v hv]
      exact smooth_monotone h β hpos hh x y
    · have hb : β=0 := le_antisymm (le_of_not_gt hpos) hβ
      rw [hb,zero_mul]
      exact (mul_nonneg hμ (sq_nonneg _)).trans hstrong
  have hm : auxS μ β x y u v ≤ ⟪x-y,u-v⟫_ℝ/2 := by
    change max (μ/2*‖x-y‖^2) (β/2*‖u-v‖^2) ≤ _
    exact max_le (by linarith) (by linarith)
  linarith

theorem contract_from_bounds (γ μ β t A B C : ℝ)
    (hγ : 0 < γ) (hμ : 0 < μ) (hβ : 0 < β) (ht : 0 < t) (ht1 : t ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (d dn : H)
    (hd : ‖d‖^2 ≤ 3*(A+γ^2*B+C))
    (he : 4*γ*t*μ*A+4*γ*t*β*B+4*t*(1-t)*C ≤ ‖d‖^2-‖dn‖^2) :
    ‖dn‖ ≤ RelaxedPRS.Linear.C43 γ μ β t * ‖d‖ := by
  let m := min (min (γ*μ) (β/γ)) (1-t)
  have hm0 : 0 ≤ m := le_min (le_min (by positivity) (by positivity)) (by linarith)
  have hm1 : m ≤ γ*μ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : m ≤ β/γ := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : m ≤ 1-t := min_le_right _ _
  have hmγ : m*γ^2 ≤ γ*β := by
    have hh := mul_le_mul_of_nonneg_right ((le_div_iff₀ hγ).mp hm2) hγ.le
    nlinarith only [hh]
  have hsum := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hm1 hA) (mul_le_mul_of_nonneg_right hmγ hB))
    (mul_le_mul_of_nonneg_right hm3 hC)
  have hd' := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 4*t/3*m)
  have hw := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4*t)
  have hn : ‖dn‖^2 ≤ (1-4*t/3*m)*‖d‖^2 := by nlinarith only [hd',hw,he]
  have htm := mul_le_mul_of_nonneg_left hm3 ht.le
  have hrad : 0 ≤ 1-4*t/3*m := by nlinarith [sq_nonneg (t-1/2)]
  change ‖dn‖ ≤ Real.sqrt (1-4*t/3*m)*‖d‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hrad]
  exact hn

end QueeliusPRS

/-- Theorem 4.3, p. 16: linear contraction when regularity is split across f and g. -/
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (μ β : ℝ) (hμ : 0 < μ) (hβ : 0 < β) :
    (RelaxedPRS.StrongCvx.HasLipGrad β g → RelaxedPRS.StrongCvx.IsStrongCvxE μ f →
      ∀ k, ‖z (k + 1) - zs‖ ≤ RelaxedPRS.Linear.C43 γ μ β (lam k) * ‖z k - zs‖) ∧
    (RelaxedPRS.StrongCvx.HasLipGrad β f → RelaxedPRS.StrongCvx.IsStrongCvxE μ g →
      ∀ k, ‖z (k + 1) - zs‖ ≤ RelaxedPRS.Linear.C43 γ μ β (lam k) * ‖z k - zs‖) := by
  have hstrongF (k : ℕ) (hsc : IsStrongCvxE μ f) :
      μ*‖xf Pf Pg (z k)-xg Pg zs‖^2 ≤
        ⟪xf Pf Pg (z k)-xg Pg zs,gtF γ Pf Pg (z k)-gtF γ Pf Pg zs⟫_ℝ := by
    have hi := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) (hlam k).1 (z k)
    have hs := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) (hlam k).1 zs
    have hb := QueeliusPRS.strong_monotone f μ hμ.le hsc _ _ _ _ hi.2.1 hs.2.1
    simpa only [QueeliusPRS.fixed_aux Pf Pg zs hzs] using hb
  have hstrongG (k : ℕ) (hsc : IsStrongCvxE μ g) :
      μ*‖xg Pg (z k)-xg Pg zs‖^2 ≤
        ⟪xg Pg (z k)-xg Pg zs,gtG γ Pg (z k)-gtG γ Pg zs⟫_ℝ := by
    have hi := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) (hlam k).1 (z k)
    have hs := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) (hlam k).1 zs
    exact QueeliusPRS.strong_monotone g μ hμ.le hsc _ _ _ _ hi.1 hs.1
  have smooth_subgrad (F : H → EReal) (hl : HasLipGrad β F) (x y u v : H)
      (hu : u ∈ subgrad F x) (hv : v ∈ subgrad F y) :
      β*‖u-v‖^2 ≤ ⟪x-y,u-v⟫_ℝ := by
    obtain ⟨h,hF,hh⟩ := hl
    have hfe : F=fun x => (h x : EReal) := funext hF
    rw [hfe] at hu hv
    rw [QueeliusPRS.subgrad_gradient h hh.2.1 x u hu,
      QueeliusPRS.subgrad_gradient h hh.2.1 y v hv]
    exact QueeliusPRS.smooth_monotone h β hβ hh x y
  constructor
  · intro hl hsc k
    have ht := (hlam k).1
    have hi := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) ht (z k)
    have hs := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) ht zs
    have hF := hstrongF k hsc
    have hG := smooth_subgrad g hl _ _ _ _ hi.1 hs.1
    have he := QueeliusPRS.step_energy Pf Pg (z k) zs γ (lam k) hγ.ne' hzs
    have hr : z (k+1)=Tlam Pf Pg (lam k) (z k) := hz k
    rw [← hr] at he
    have hFG := mul_le_mul_of_nonneg_left (add_le_add hF hG)
      (by positivity : 0 ≤ 4*γ*lam k)
    have hd : z k-zs=(xf Pf Pg (z k)-xg Pg zs)+
        γ • (gtG γ Pg (z k)-gtG γ Pg zs)+(xg Pg (z k)-xf Pf Pg (z k)) := by
      dsimp [gtG,xg]
      simp only [smul_sub,smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]
      module
    have hn := QueeliusPRS.norm_three (xf Pf Pg (z k)-xg Pg zs)
      (γ • (gtG γ Pg (z k)-gtG γ Pg zs)) (xg Pg (z k)-xf Pf Pg (z k))
    rw [← hd,norm_smul,Real.norm_of_nonneg hγ.le,mul_pow,norm_sub_rev (xg Pg (z k)) (xf Pf Pg (z k))] at hn
    apply QueeliusPRS.contract_from_bounds γ μ β (lam k) _ _ _ hγ hμ hβ ht (hlam k).2
      (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (z k-zs) (z (k+1)-zs) hn
    nlinarith only [hFG,he]
  · intro hl hsc k
    have ht := (hlam k).1
    have hi := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) ht (z k)
    have hs := accepted_prs_identities f g hf hg γ hγ Pf Pg hPf hPg (lam k) ht zs
    have hF := smooth_subgrad f hl _ _ _ _ hi.2.1 hs.2.1
    rw [QueeliusPRS.fixed_aux Pf Pg zs hzs] at hF
    have hG := hstrongG k hsc
    have he := QueeliusPRS.step_energy Pf Pg (z k) zs γ (lam k) hγ.ne' hzs
    have hr : z (k+1)=Tlam Pf Pg (lam k) (z k) := hz k
    rw [← hr] at he
    have hFG := mul_le_mul_of_nonneg_left (add_le_add hF hG)
      (by positivity : 0 ≤ 4*γ*lam k)
    have hd : z k-zs=(xg Pg (z k)-xg Pg zs)+
        (-γ) • (gtF γ Pf Pg (z k)-gtF γ Pf Pg zs)+(xg Pg (z k)-xf Pf Pg (z k)) := by
      have hp (w : H) : γ • gtF γ Pf Pg w=RelaxedPRS.StrongCvx.refl Pg w-xf Pf Pg w := by
        simp only [gtF,smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]
      simp only [neg_smul,smul_sub,hp]
      rw [QueeliusPRS.fixed_aux Pf Pg zs hzs]
      dsimp [RelaxedPRS.StrongCvx.refl,xg]
      module
    have hn := QueeliusPRS.norm_three (xg Pg (z k)-xg Pg zs)
      ((-γ) • (gtF γ Pf Pg (z k)-gtF γ Pf Pg zs)) (xg Pg (z k)-xf Pf Pg (z k))
    rw [← hd,norm_smul,norm_neg,Real.norm_of_nonneg hγ.le,mul_pow,norm_sub_rev (xg Pg (z k)) (xf Pf Pg (z k))] at hn
    apply QueeliusPRS.contract_from_bounds γ μ β (lam k) _ _ _ hγ hμ hβ ht (hlam k).2
      (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (z k-zs) (z (k+1)-zs) hn
    nlinarith only [hFG,he]
