-- Prove2me | solution 1 for ProxAlg.FixedPoint.forward_backward_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:12:04.312169+00:00
-- url     : https://prove2.me/submissions/2f898dda-b942-4329-9805-464bc1f7b793

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_ProxAlg_FixedPoint_Basic

set_option autoImplicit false

/-- If `0 ≤ K + t * M` for all `t ∈ (0, 1]` with `M ≥ 0`, then `0 ≤ K`. -/
theorem fbf_nonneg_of_forall {K M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ K + t * M) : 0 ≤ K := by
  by_contra hK'
  have hK : K < 0 := not_le.mp hK'
  set s : ℝ := -K / (2 * (M + 1)) with hs
  have hM1 : 0 < 2 * (M + 1) := by linarith
  have hs0 : 0 < s := div_pos (neg_pos.mpr hK) hM1
  have hsM : s * (2 * (M + 1)) = -K := by
    rw [hs]; field_simp
  set t : ℝ := min 1 s with ht
  have ht0 : 0 < t := lt_min one_pos hs0
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ s := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t * M ≤ s * M := mul_le_mul_of_nonneg_right ht2 hM
  nlinarith

open scoped RealInnerProductSpace in
theorem fbf_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem fbf_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (by simpa using fbf_line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

/-- Moving a real summand across an inequality in `EReal`. -/
theorem fbf_shift (P Q : ℝ) (a b : EReal) :
    ((P : ℝ) : EReal) + a ≤ ((Q : ℝ) : EReal) + b ↔ a ≤ ((Q - P : ℝ) : EReal) + b := by
  generalize hR : Q - P = R
  have hQ : Q = R + P := by linarith
  subst hQ
  induction a using EReal.rec with
  | bot => simp
  | top =>
    induction b using EReal.rec with
    | bot => simp
    | top => simp
    | coe b =>
      rw [EReal.coe_add_top, top_le_iff, top_le_iff]
      rw [← EReal.coe_add, ← EReal.coe_add]
      exact iff_of_false (EReal.coe_ne_top _) (EReal.coe_ne_top _)
  | coe a =>
    induction b using EReal.rec with
    | bot => simp
    | top => simp
    | coe b =>
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff,
        EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

open MoreauProx.Decomposition in open scoped RealInnerProductSpace in
theorem fbf_isProx_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (lam : ℝ) (xs d : H) :
    IsProx (fun u => ((lam : ℝ) : EReal) * g u) (xs - lam • d) xs ↔
      ∀ u, ((lam : ℝ) : EReal) * g xs ≤
        ((‖u - xs‖ ^ 2 / 2 + lam * ⟪u - xs, d⟫ : ℝ) : EReal) + ((lam : ℝ) : EReal) * g u := by
  unfold IsProx
  refine forall_congr' fun u => ?_
  unfold proxObjective
  beta_reduce
  rw [fbf_shift]
  have h1 : xs - (xs - lam • d) = lam • d := by abel
  have h2 : u - (xs - lam • d) = (u - xs) + lam • d := by abel
  have h3 : ‖u - (xs - lam • d)‖ ^ 2 / 2 - ‖xs - (xs - lam • d)‖ ^ 2 / 2
      = ‖u - xs‖ ^ 2 / 2 + lam * ⟪u - xs, d⟫ := by
    rw [h1, h2, norm_add_sq_real, real_inner_smul_right, norm_smul]
    ring
  rw [h3]

open MoreauProx.Decomposition in
theorem fbf_conv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (hg : GammaZero g) (p q : H) (a b t : ℝ) (hp : g p = (a : EReal))
    (hq : g q = (b : EReal)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    g ((1 - t) • p + t • q) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hxe : (p, a) ∈ {x : H × ℝ | g x.1 ≤ (x.2 : EReal)} := by
    simp only [Set.mem_ofPred_eq, hp, le_refl]
  have hue : (q, b) ∈ {x : H × ℝ | g x.1 ≤ (x.2 : EReal)} := by
    simp only [Set.mem_ofPred_eq, hq, le_refl]
  have hconv := hg.convex_epigraph hxe hue (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hconv
  exact hconv

open MoreauProx.Decomposition in open scoped RealInnerProductSpace in
theorem fbf_forward {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfd : Differentiable ℝ f) (g : H → EReal) (hg : GammaZero g)
    (lam : ℝ) (hlam : 0 < lam) (xs : H)
    (hmin : ∀ y, ((f xs : ℝ) : EReal) + g xs ≤ ((f y : ℝ) : EReal) + g y) :
    ∀ u, ((lam : ℝ) : EReal) * g xs ≤
        ((‖u - xs‖ ^ 2 / 2 + lam * ⟪u - xs, gradient f xs⟫ : ℝ) : EReal)
          + ((lam : ℝ) : EReal) * g u := by
  have hF : ∀ x, HasGradientAt f (gradient f x) x := fun x => (hfd x).hasGradientAt
  obtain ⟨x0, hx0⟩ := hg.exists_ne_top
  have hx0' : g x0 = ((g x0).toReal : EReal) := (EReal.coe_toReal hx0 (hg.ne_bot x0)).symm
  have hxs : g xs ≠ ⊤ := by
    intro htop
    have h := hmin x0
    rw [htop, EReal.coe_add_top, hx0', ← EReal.coe_add, top_le_iff] at h
    exact EReal.coe_ne_top _ h
  have hxs' : g xs = ((g xs).toReal : EReal) := (EReal.coe_toReal hxs (hg.ne_bot xs)).symm
  set a : ℝ := (g xs).toReal with ha
  intro u
  have hne := hg.ne_bot u
  induction hu : g u using EReal.rec with
  | bot => exact absurd hu hne
  | top =>
    rw [EReal.coe_mul_top_of_pos hlam, EReal.coe_add_top]
    exact le_top
  | coe b =>
    set w := u - xs with hw
    have key : a - b ≤ ⟪gradient f xs, w⟫ := by
      have hd := fbf_line_deriv hF xs w 0
      simp only [zero_smul, add_zero] at hd
      have hlim := hd.tendsto_slope_zero_right
      have hI : Set.Ioc (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioc_mem_nhdsGT zero_lt_one
      simp only [zero_add, zero_smul, add_zero] at hlim
      refine ge_of_tendsto hlim ?_
      filter_upwards [hI] with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hconv := fbf_conv g hg xs u a b t hxs' hu ht0.le ht1
      have hy : (1 - t) • xs + t • u = xs + t • w := by
        simp only [hw, sub_smul, one_smul, smul_sub]; abel
      rw [hy] at hconv
      have h3 : ((f xs : ℝ) : EReal) + ((a : ℝ) : EReal) ≤
          ((f (xs + t • w) : ℝ) : EReal) + (((1 - t) * a + t * b : ℝ) : EReal) := by
        have := hmin (xs + t • w)
        rw [hxs'] at this
        exact this.trans (add_le_add le_rfl hconv)
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
      simp only [smul_eq_mul]
      rw [← div_eq_inv_mul, le_div_iff₀ ht0]
      nlinarith
    rw [hxs', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [real_inner_comm] at key
    nlinarith [mul_le_mul_of_nonneg_left key hlam.le, sq_nonneg ‖w‖]

open MoreauProx.Decomposition in open scoped RealInnerProductSpace in
theorem fbf_backward {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hf : ConvexOn ℝ Set.univ f) (hfd : Differentiable ℝ f)
    (g : H → EReal) (hg : GammaZero g)
    (lam : ℝ) (hlam : 0 < lam) (xs : H)
    (hprox : ∀ u, ((lam : ℝ) : EReal) * g xs ≤
        ((‖u - xs‖ ^ 2 / 2 + lam * ⟪u - xs, gradient f xs⟫ : ℝ) : EReal)
          + ((lam : ℝ) : EReal) * g u) :
    ∀ y, ((f xs : ℝ) : EReal) + g xs ≤ ((f y : ℝ) : EReal) + g y := by
  have hF : ∀ x, HasGradientAt f (gradient f x) x := fun x => (hfd x).hasGradientAt
  obtain ⟨x0, hx0⟩ := hg.exists_ne_top
  have hx0' : g x0 = ((g x0).toReal : EReal) := (EReal.coe_toReal hx0 (hg.ne_bot x0)).symm
  have hxs : g xs ≠ ⊤ := by
    intro htop
    have h := hprox x0
    rw [htop, EReal.coe_mul_top_of_pos hlam, hx0', ← EReal.coe_mul, ← EReal.coe_add,
      top_le_iff] at h
    exact EReal.coe_ne_top _ h
  have hxs' : g xs = ((g xs).toReal : EReal) := (EReal.coe_toReal hxs (hg.ne_bot xs)).symm
  set a : ℝ := (g xs).toReal with ha
  intro y
  have hne := hg.ne_bot y
  induction hy : g y using EReal.rec with
  | bot => exact absurd hy hne
  | top =>
    rw [EReal.coe_add_top]
    exact le_top
  | coe b =>
    set w := y - xs with hw
    have key : 0 ≤ b + ⟪w, gradient f xs⟫ - a := by
      refine fbf_nonneg_of_forall (M := ‖w‖ ^ 2 / (2 * lam)) (by positivity) ?_
      intro t ht0 ht1
      have hconv := fbf_conv g hg xs y a b t hxs' hy ht0.le ht1
      have hne2 := hg.ne_bot ((1 - t) • xs + t • y)
      induction hu : g ((1 - t) • xs + t • y) using EReal.rec with
      | bot => exact absurd hu hne2
      | top =>
        rw [hu] at hconv
        exact absurd (top_le_iff.mp hconv) (EReal.coe_ne_top _)
      | coe e =>
        rw [hu, EReal.coe_le_coe_iff] at hconv
        have hp := hprox ((1 - t) • xs + t • y)
        rw [hu, hxs', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
          EReal.coe_le_coe_iff] at hp
        have hd : (1 - t) • xs + t • y - xs = t • w := by
          simp only [hw, sub_smul, one_smul, smul_sub]; abel
        rw [hd, norm_smul, real_inner_smul_left, Real.norm_eq_abs, mul_pow, sq_abs] at hp
        by_contra hneg'
        have hneg := not_le.mp hneg'
        have hlm : lam * ((‖w‖ ^ 2 / (2 * lam))) = ‖w‖ ^ 2 / 2 := by
          field_simp
        have : t * lam * (b + ⟪w, gradient f xs⟫ - a + t * (‖w‖ ^ 2 / (2 * lam))) < 0 :=
          mul_neg_of_pos_of_neg (mul_pos ht0 hlam) hneg
        nlinarith
    have hfo := fbf_convex_fo hF hf xs y
    rw [hxs']
    simp only [← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [real_inner_comm] at key
    linarith

open ProxAlg.FixedPoint MoreauProx.Decomposition in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : MoreauProx.Decomposition.GammaZero g)
    (lam : ℝ) (hlam : 0 < lam) (xs : EuclideanSpace ℝ (Fin n)) :
    (∀ y, ((f xs : ℝ) : EReal) + g xs ≤ ((f y : ℝ) : EReal) + g y) ↔
      MoreauProx.Decomposition.IsProx
        (fun u => ((lam : ℝ) : EReal) * g u)
        (xs - lam • gradient f xs) xs := by
  rw [fbf_isProx_iff]
  exact ⟨fbf_forward f hfd g hg lam hlam xs, fbf_backward f hf hfd g hg lam hlam xs⟩
