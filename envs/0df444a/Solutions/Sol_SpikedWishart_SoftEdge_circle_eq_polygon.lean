-- Prove2me | solution 1 for SpikedWishart.SoftEdge.circle_eq_polygon
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T08:14:21.627205+00:00
-- url     : https://prove2.me/submissions/d2c94510-c7de-42ed-8160-53d01047f95c

import Mathlib

set_option linter.all false
set_option Elab.async false

set_option autoImplicit false

namespace P31

open Complex Metric Set Filter Topology

/-- Two primitives of `f` on an open preconnected set differ by a constant there. -/
theorem prim_sub_const {f F G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) (hG : ∀ z ∈ U, HasDerivAt G (f z) z)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) : F x - G x = F y - G y := by
  refine hU.is_const_of_deriv_eq_zero hU' (f := fun z => F z - G z) ?_ ?_ hx hy
  · intro z hz; exact ((hF z hz).sub (hG z hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    have h : HasDerivAt (fun z => F z - G z) (f z - f z) z := (hF z hz).sub (hG z hz)
    simp only [Pi.zero_apply]; rw [h.deriv, sub_self]

theorem mem_ballY {Y : ℝ} (hY : 0 < Y) {z : ℂ} :
    z ∈ ball (I * (Y : ℂ)) Y ↔ z.re ^ 2 + z.im ^ 2 < 2 * Y * z.im := by
  rw [mem_ball, dist_eq]
  constructor
  · intro h
    have h2 : ‖z - I * Y‖ ^ 2 < Y ^ 2 := by gcongr
    rw [← normSq_eq_norm_sq, normSq_apply] at h2
    simp at h2; nlinarith
  · intro h
    have h2 : ‖z - I * Y‖ ^ 2 < Y ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hY.le h2

theorem im_pos_of_mem_ballY {Y : ℝ} {z : ℂ} (hz : z ∈ ball (I * (Y : ℂ)) Y) : 0 < z.im := by
  have hY : 0 < Y := pos_of_mem_ball hz
  rw [mem_ballY hY] at hz
  by_contra him0
  have him : z.im ≤ 0 := not_lt.mp him0
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hY.le him, sq_nonneg z.re, sq_nonneg z.im]

theorem ballY_mono {Y Y' : ℝ} (h : Y ≤ Y') : ball (I * (Y : ℂ)) Y ⊆ ball (I * (Y' : ℂ)) Y' := by
  intro z hz
  have hY : 0 < Y := pos_of_mem_ball hz
  have him := im_pos_of_mem_ballY hz
  rw [mem_ballY hY] at hz; rw [mem_ballY (by linarith)]
  nlinarith

/-- The radius used for the point `z`: the ball of that radius contains `z` and `I`. -/
noncomputable def Yof (z : ℂ) : ℝ := (z.re ^ 2 + z.im ^ 2 + 1) / z.im + 1

theorem one_le_Yof {z : ℂ} (hz : 0 < z.im) : 1 ≤ Yof z := by
  unfold Yof; have : 0 ≤ (z.re ^ 2 + z.im ^ 2 + 1) / z.im := by positivity
  linarith

theorem mem_ball_Yof {z : ℂ} (hz : 0 < z.im) : z ∈ ball (I * (Yof z : ℂ)) (Yof z) := by
  have h1 := one_le_Yof hz
  rw [mem_ballY (by linarith)]; unfold Yof
  have : (z.re ^ 2 + z.im ^ 2 + 1) / z.im * z.im = z.re ^ 2 + z.im ^ 2 + 1 := div_mul_cancel₀ _ hz.ne'
  nlinarith

theorem I_mem_ballY {Y : ℝ} (hY : 1 ≤ Y) : I ∈ ball (I * (Y : ℂ)) Y := by
  rw [mem_ballY (by linarith)]; simp; linarith

/-- **Primitives on the upper half-plane.** -/
theorem exact_upper {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | 0 < z.im}) :
    ∃ F : ℂ → ℂ, ∀ z, 0 < z.im → HasDerivAt F (f z) z := by
  have hsub : ∀ Y : ℝ, ball (I * (Y : ℂ)) Y ⊆ {z | 0 < z.im} := by
    intro Y z hz; exact im_pos_of_mem_ballY hz
  have hex : ∀ Y : ℝ, ∃ G : ℂ → ℂ, G I = 0 ∧ ∀ z ∈ ball (I * (Y : ℂ)) Y, HasDerivAt G (f z) z :=
    fun Y => ((hf.mono (hsub Y)).isExactOn_ball).with_val_at I 0
  choose G hG0 hG using hex
  have hcons : ∀ Y Y' : ℝ, 1 ≤ Y → Y ≤ Y' → ∀ z ∈ ball (I * (Y : ℂ)) Y, G Y z = G Y' z := by
    intro Y Y' hY hYY' z hz
    have h := prim_sub_const isOpen_ball (convex_ball _ _).isPreconnected (hG Y)
      (fun w hw => hG Y' w (ballY_mono hYY' hw)) hz (I_mem_ballY hY)
    rw [hG0, hG0] at h; linear_combination h
  have hcons2 : ∀ Y Y' : ℝ, 1 ≤ Y → 1 ≤ Y' → ∀ z, z ∈ ball (I * (Y : ℂ)) Y →
      z ∈ ball (I * (Y' : ℂ)) Y' → G Y z = G Y' z := by
    intro Y Y' hY hY' z hz hz'
    rcases le_total Y Y' with h | h
    · exact hcons Y Y' hY h z hz
    · exact (hcons Y' Y hY' h z hz').symm
  refine ⟨fun z => G (Yof z) z, fun z hz => ?_⟩
  have hball := mem_ball_Yof hz
  have hev : (fun w => G (Yof w) w) =ᶠ[𝓝 z] G (Yof z) := by
    filter_upwards [isOpen_ball.mem_nhds hball] with w hw
    have hw0 : 0 < w.im := hsub _ hw
    exact hcons2 _ _ (one_le_Yof hw0) (one_le_Yof hz) w (mem_ball_Yof hw0) hw
  exact (hG _ z hball).congr_of_eventuallyEq hev

/-- **Primitives on any open half-plane** `{z | 0 < ((z - p) / e).im}`. -/
theorem exact_half (p e : ℂ) (he : e ≠ 0) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < ((z - p) / e).im}) :
    ∃ F : ℂ → ℂ, ∀ z, 0 < ((z - p) / e).im → HasDerivAt F (f z) z := by
  have hg : DifferentiableOn ℂ (fun w => f (p + e * w) * e) {w | 0 < w.im} := by
    intro w hw
    have hmem : p + e * w ∈ {z | 0 < ((z - p) / e).im} := by
      show 0 < ((p + e * w - p) / e).im
      rwa [show (p + e * w - p) / e = w by field_simp; ring]
    have h1 : DifferentiableWithinAt ℂ (fun w : ℂ => p + e * w) {w | 0 < w.im} w :=
      ((differentiableAt_const p).add ((differentiableAt_const e).mul differentiableAt_id)).differentiableWithinAt
    exact ((hf _ hmem).comp w h1 (fun x hx => by
      show 0 < ((p + e * x - p) / e).im
      rwa [show (p + e * x - p) / e = x by field_simp; ring])).mul
        (differentiableWithinAt_const e)
  obtain ⟨G, hG⟩ := exact_upper hg
  refine ⟨fun z => G ((z - p) / e), fun z hz => ?_⟩
  have h1 : HasDerivAt (fun z : ℂ => (z - p) / e) (1 / e) z := by
    simpa using ((hasDerivAt_id z).sub_const p).div_const e
  have h2 := (hG _ hz).comp z h1
  rw [show p + e * ((z - p) / e) = z by field_simp; ring] at h2
  rw [show f z * e * (1 / e) = f z by field_simp] at h2
  exact h2

/-- Fundamental theorem along a C¹ path through a region where `F' = h`. -/
theorem path_integral_prim {F h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) (hc : ContinuousOn h U)
    (γ γ' : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hγ'c : Continuous γ') (hγU : ∀ t ∈ Icc a b, γ t ∈ U) :
    ∫ t in a..b, h (γ t) * γ' t = F (γ b) - F (γ a) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F ∘ γ) (fun t ht => ?_) ?_
  · rw [uIcc_of_le hab] at ht
    exact (hF _ (hγU t ht)).comp t (hγ t)
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    refine ContinuousOn.mul ?_ hγ'c.continuousOn
    exact hc.comp hγc.continuousOn (fun t ht => hγU t ht)

/-- Segment from `p` to `q`, parametrised on `[0, 1]`. -/
theorem seg_integral_prim {F h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) (hc : ContinuousOn h U) (p q : ℂ)
    (hpq : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → p + (t : ℂ) * (q - p) ∈ U) :
    ∫ t in (0 : ℝ)..1, h (p + (t : ℂ) * (q - p)) * (q - p) = F q - F p := by
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => p + (t : ℂ) * (q - p)) (q - p) t := by
    intro t
    have := ((hasDerivAt_id t).ofReal_comp).mul_const (q - p)
    simpa using this.const_add p
  have := path_integral_prim hU hF hc (fun t : ℝ => p + (t : ℂ) * (q - p)) (fun _ => q - p) 0 1
    zero_le_one hγ continuous_const hpq
  simpa using this

/-- Arc of the circle `circleMap c R` over `[α, β]`. -/
theorem arc_integral_prim {F h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) (hc : ContinuousOn h U) (c : ℂ) (R α β : ℝ)
    (hαβ : α ≤ β) (harc : ∀ θ ∈ Icc α β, circleMap c R θ ∈ U) :
    ∫ θ in α..β, deriv (circleMap c R) θ • h (circleMap c R θ) =
      F (circleMap c R β) - F (circleMap c R α) := by
  have h1 := path_integral_prim hU hF hc (circleMap c R) (fun θ => circleMap 0 R θ * I) α β hαβ
    (fun θ => hasDerivAt_circleMap c R θ) (by fun_prop) harc
  rw [← h1]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [smul_eq_mul, deriv_circleMap]
  ring


/-! ## K2: a closed circle around a real segment integrates to the four-primitive chain constant -/

theorem cm_re_im (c ρ θ : ℝ) : (circleMap (c : ℂ) ρ θ).re = c + ρ * Real.cos θ ∧
    (circleMap (c : ℂ) ρ θ).im = ρ * Real.sin θ := by
  unfold circleMap
  constructor
  · rw [Complex.add_re, Complex.mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_re, ofReal_im]
    ring
  · rw [Complex.add_im, Complex.mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      ofReal_re, ofReal_im, ofReal_im]
    ring

/-- Primitives of `h` on the four half-planes around the real segment `[a, b]`. -/
theorem quad_prims {h : ℂ → ℂ} {a b : ℝ}
    (hd : DifferentiableOn ℂ h {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re}) :
    ∃ F1 F2 F3 F4 : ℂ → ℂ, (∀ z : ℂ, z.re < a → HasDerivAt F1 (h z) z) ∧
      (∀ z : ℂ, 0 < z.im → HasDerivAt F2 (h z) z) ∧
      (∀ z : ℂ, b < z.re → HasDerivAt F3 (h z) z) ∧
      (∀ z : ℂ, z.im < 0 → HasDerivAt F4 (h z) z) := by
  have e1 : ∀ z : ℂ, ((z - (a : ℂ)) / I).im = a - z.re := by
    intro z; rw [Complex.div_I]; simp
  have e3 : ∀ z : ℂ, ((z - (b : ℂ)) / (-I)).im = z.re - b := by
    intro z; rw [div_neg, Complex.div_I]; simp
  have e2 : ∀ z : ℂ, ((z - 0) / 1).im = z.im := by intro z; simp
  have e4 : ∀ z : ℂ, ((z - 0) / (-1)).im = -z.im := by
    intro z; rw [sub_zero, div_neg, div_one, Complex.neg_im]
  obtain ⟨F1, h1⟩ := exact_half (a : ℂ) I I_ne_zero (f := h)
    (hd.mono (fun z hz => Or.inr (Or.inl (by
      have := e1 z; simp only [Set.mem_ofPred_eq] at hz; linarith))))
  obtain ⟨F2, h2⟩ := exact_half 0 1 one_ne_zero (f := h)
    (hd.mono (fun z hz => Or.inl (by
      have := e2 z; simp only [Set.mem_ofPred_eq] at hz; intro h0; linarith)))
  obtain ⟨F3, h3⟩ := exact_half (b : ℂ) (-I) (neg_ne_zero.2 I_ne_zero) (f := h)
    (hd.mono (fun z hz => Or.inr (Or.inr (by
      have := e3 z; simp only [Set.mem_ofPred_eq] at hz; linarith))))
  obtain ⟨F4, h4⟩ := exact_half 0 (-1) (neg_ne_zero.2 one_ne_zero) (f := h)
    (hd.mono (fun z hz => Or.inl (by
      have := e4 z; simp only [Set.mem_ofPred_eq] at hz; intro h0; linarith)))
  exact ⟨F1, F2, F3, F4, fun z hz => h1 z (by rw [e1]; linarith),
    fun z hz => h2 z (by rw [e2]; exact hz), fun z hz => h3 z (by rw [e3]; linarith),
    fun z hz => h4 z (by rw [e4]; linarith)⟩

/-- The value `F_i(p) - F_j(p)` does not depend on `p` in the quadrant `D_i ∩ D_j`. -/
theorem quad_const {h F G : ℂ → ℂ} {P Q : Set ℂ} (hP : IsOpen P) (hQ : IsOpen Q)
    (hPc : Convex ℝ P) (hQc : Convex ℝ Q)
    (hF : ∀ z ∈ P, HasDerivAt F (h z) z) (hG : ∀ z ∈ Q, HasDerivAt G (h z) z)
    {x y : ℂ} (hx : x ∈ P ∩ Q) (hy : y ∈ P ∩ Q) : F x - G x = F y - G y :=
  prim_sub_const (hP.inter hQ) ((hPc.inter hQc).isPreconnected)
    (fun z hz => hF z hz.1) (fun z hz => hG z hz.2) hx hy

set_option maxHeartbeats 1000000 in
/-- **K2 (circle form).** For `h` holomorphic off the real segment `[a, b]` and a circle with real
centre enclosing that segment, the circle integral equals the chain constant
`(F₃-F₂)(p₁) + (F₂-F₁)(p₂) + (F₁-F₄)(p₃) + (F₄-F₃)(p₀)` for any junction points in the quadrants. -/
theorem circle_chain {h F1 F2 F3 F4 : ℂ → ℂ} {a b c ρ : ℝ}
    (hab : a ≤ b) (ha : c - ρ < a) (hb : b < c + ρ)
    (hcont : ContinuousOn h {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re})
    (hF1 : ∀ z : ℂ, z.re < a → HasDerivAt F1 (h z) z)
    (hF2 : ∀ z : ℂ, 0 < z.im → HasDerivAt F2 (h z) z)
    (hF3 : ∀ z : ℂ, b < z.re → HasDerivAt F3 (h z) z)
    (hF4 : ∀ z : ℂ, z.im < 0 → HasDerivAt F4 (h z) z)
    (p0 p1 p2 p3 : ℂ) (hp0 : p0.im < 0 ∧ b < p0.re) (hp1 : b < p1.re ∧ 0 < p1.im)
    (hp2 : 0 < p2.im ∧ p2.re < a) (hp3 : p3.re < a ∧ p3.im < 0) :
    (∮ z in C((c : ℂ), ρ), h z) =
      (F3 p1 - F2 p1) + (F2 p2 - F1 p2) + (F1 p3 - F4 p3) + (F4 p0 - F3 p0) := by
  have hρ : 0 < ρ := by linarith
  -- the opening angle α
  set m : ℝ := max (max ((b - c) / ρ) ((c - a) / ρ)) 0 with hm
  have hm1 : m < 1 := by
    rw [hm]
    refine max_lt (max_lt ?_ ?_) one_pos
    · rw [div_lt_one hρ]; linarith
    · rw [div_lt_one hρ]; linarith
  have hm0 : 0 ≤ m := le_max_right _ _
  set x : ℝ := (m + 1) / 2 with hx
  set α : ℝ := Real.arccos x with hα
  have hcosα : Real.cos α = x := Real.cos_arccos (by rw [hx]; linarith) (by rw [hx]; linarith)
  have hα0 : 0 < α := Real.arccos_pos.2 (by rw [hx]; linarith)
  have hαπ : α ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 (by rw [hx]; linarith)
  have hpi := Real.pi_pos
  have hxb : b - c < ρ * x := by
    have h1 : (b - c) / ρ ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
    have h2 : (b - c) / ρ < x := by rw [hx]; linarith
    rwa [div_lt_iff₀ hρ, mul_comm] at h2
  have hxa : c - a < ρ * x := by
    have h1 : (c - a) / ρ ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 : (c - a) / ρ < x := by rw [hx]; linarith
    rwa [div_lt_iff₀ hρ, mul_comm] at h2
  -- domains
  have oL : IsOpen {z : ℂ | z.re < a} := isOpen_lt Complex.continuous_re continuous_const
  have oU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have oR : IsOpen {z : ℂ | b < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have oD : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have cL : ContinuousOn h {z : ℂ | z.re < a} := hcont.mono (fun z hz => Or.inr (Or.inl hz))
  have cU : ContinuousOn h {z : ℂ | 0 < z.im} := hcont.mono (fun z hz => Or.inl (ne_of_gt hz))
  have cR : ContinuousOn h {z : ℂ | b < z.re} := hcont.mono (fun z hz => Or.inr (Or.inr hz))
  have cD : ContinuousOn h {z : ℂ | z.im < 0} := hcont.mono (fun z hz => Or.inl (ne_of_lt hz))
  -- trig facts
  have cos_near0 : ∀ θ : ℝ, -α ≤ θ → θ ≤ α → x ≤ Real.cos θ := by
    intro θ h1 h2
    rw [← hcosα, ← Real.cos_abs θ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith) (abs_le.2 ⟨h1, h2⟩)
  have cos_nearπ : ∀ θ : ℝ, Real.pi - α ≤ θ → θ ≤ Real.pi + α → Real.cos θ ≤ -x := by
    intro θ h1 h2
    have := cos_near0 (θ - Real.pi) (by linarith) (by linarith)
    rw [Real.cos_sub_pi] at this
    linarith
  have sin_up : ∀ θ : ℝ, α ≤ θ → θ ≤ Real.pi - α → 0 < Real.sin θ := fun θ h1 h2 =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sin_dn : ∀ θ : ℝ, Real.pi + α ≤ θ → θ ≤ 2 * Real.pi - α → Real.sin θ < 0 := by
    intro θ h1 h2
    have := sin_up (θ - Real.pi) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this
    linarith
  -- arc memberships
  have mR : ∀ θ ∈ Set.Icc (-α) α, circleMap (c : ℂ) ρ θ ∈ {z : ℂ | b < z.re} := by
    intro θ hθ
    show b < (circleMap (c : ℂ) ρ θ).re
    rw [(cm_re_im c ρ θ).1]
    have := mul_le_mul_of_nonneg_left (cos_near0 θ hθ.1 hθ.2) hρ.le
    linarith
  have mU : ∀ θ ∈ Set.Icc α (Real.pi - α), circleMap (c : ℂ) ρ θ ∈ {z : ℂ | 0 < z.im} := by
    intro θ hθ
    show 0 < (circleMap (c : ℂ) ρ θ).im
    rw [(cm_re_im c ρ θ).2]
    exact mul_pos hρ (sin_up θ hθ.1 hθ.2)
  have mL : ∀ θ ∈ Set.Icc (Real.pi - α) (Real.pi + α),
      circleMap (c : ℂ) ρ θ ∈ {z : ℂ | z.re < a} := by
    intro θ hθ
    show (circleMap (c : ℂ) ρ θ).re < a
    rw [(cm_re_im c ρ θ).1]
    have := mul_le_mul_of_nonneg_left (cos_nearπ θ hθ.1 hθ.2) hρ.le
    linarith
  have mD : ∀ θ ∈ Set.Icc (Real.pi + α) (2 * Real.pi - α),
      circleMap (c : ℂ) ρ θ ∈ {z : ℂ | z.im < 0} := by
    intro θ hθ
    show (circleMap (c : ℂ) ρ θ).im < 0
    rw [(cm_re_im c ρ θ).2]
    exact mul_neg_of_pos_of_neg hρ (sin_dn θ hθ.1 hθ.2)
  -- the four arcs
  have A1 := arc_integral_prim oR (fun z hz => hF3 z hz) cR (c : ℂ) ρ (-α) α (by linarith) mR
  have A2 := arc_integral_prim oU (fun z hz => hF2 z hz) cU (c : ℂ) ρ α (Real.pi - α)
    (by linarith) mU
  have A3 := arc_integral_prim oL (fun z hz => hF1 z hz) cL (c : ℂ) ρ (Real.pi - α)
    (Real.pi + α) (by linarith) mL
  have A4 := arc_integral_prim oD (fun z hz => hF4 z hz) cD (c : ℂ) ρ (Real.pi + α)
    (2 * Real.pi - α) (by linarith) mD
  -- continuity of the circle integrand
  set g : ℝ → ℂ := fun θ => deriv (circleMap (c : ℂ) ρ) θ • h (circleMap (c : ℂ) ρ θ) with hg
  have hmem : ∀ θ : ℝ, circleMap (c : ℂ) ρ θ ∈ {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re} := by
    intro θ
    obtain ⟨hre, him⟩ := cm_re_im c ρ θ
    by_cases hs : Real.sin θ = 0
    · have hc2 : Real.cos θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
      have hc' : Real.cos θ = 1 ∨ Real.cos θ = -1 := by
        have : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by ring_nf; linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · left; linarith
        · right; linarith
      rcases hc' with h1 | h1
      · right; right; show b < (circleMap (c : ℂ) ρ θ).re; rw [hre, h1]; linarith
      · right; left; show (circleMap (c : ℂ) ρ θ).re < a; rw [hre, h1]; linarith
    · left; show (circleMap (c : ℂ) ρ θ).im ≠ 0; rw [him]; exact mul_ne_zero hρ.ne' hs
  have hgc : Continuous g := by
    have e : g = fun θ => (circleMap 0 ρ θ * I) • h (circleMap (c : ℂ) ρ θ) := by
      funext θ; rw [hg]; simp only [deriv_circleMap]
    rw [e]
    exact ((continuous_circleMap 0 ρ).mul continuous_const).smul
      (hcont.comp_continuous (continuous_circleMap (c : ℂ) ρ) hmem)
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro θ
    rw [hg]
    simp only [deriv_circleMap, periodic_circleMap (c : ℂ) ρ θ, periodic_circleMap 0 ρ θ]
  have hii : ∀ s t : ℝ, IntervalIntegrable g MeasureTheory.volume s t :=
    fun s t => hgc.intervalIntegrable s t
  have hcirc : (∮ z in C((c : ℂ), ρ), h z) = ∫ θ in (-α)..(2 * Real.pi - α), g θ := by
    unfold circleIntegral
    have := hper.intervalIntegral_add_eq 0 (-α)
    rw [zero_add] at this
    rw [show 2 * Real.pi - α = -α + 2 * Real.pi by ring]
    exact this
  have hsplit : (∫ θ in (-α)..(2 * Real.pi - α), g θ) =
      (∫ θ in (-α)..α, g θ) + (∫ θ in α..(Real.pi - α), g θ) +
        (∫ θ in (Real.pi - α)..(Real.pi + α), g θ) +
          ∫ θ in (Real.pi + α)..(2 * Real.pi - α), g θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  have hq0 : circleMap (c : ℂ) ρ (2 * Real.pi - α) = circleMap (c : ℂ) ρ (-α) := by
    rw [show 2 * Real.pi - α = -α + 2 * Real.pi by ring]
    exact periodic_circleMap (c : ℂ) ρ (-α)
  rw [hcirc, hsplit]
  simp only [hg] at A1 A2 A3 A4 ⊢
  rw [A1, A2, A3, A4, hq0]
  -- move the junction constants to the given points
  have convL : Convex ℝ {z : ℂ | z.re < a} := convex_halfSpace_re_lt a
  have convU : Convex ℝ {z : ℂ | 0 < z.im} := convex_halfSpace_im_gt 0
  have convR : Convex ℝ {z : ℂ | b < z.re} := convex_halfSpace_re_gt b
  have convD : Convex ℝ {z : ℂ | z.im < 0} := convex_halfSpace_im_lt 0
  have j1 := quad_const (h := h) oR oU convR convU (fun z hz => hF3 z hz) (fun z hz => hF2 z hz)
    (x := circleMap (c : ℂ) ρ α) (y := p1) ⟨mR α ⟨by linarith, le_rfl⟩, mU α ⟨le_rfl, by linarith⟩⟩
    ⟨hp1.1, hp1.2⟩
  have j2 := quad_const (h := h) oU oL convU convL (fun z hz => hF2 z hz) (fun z hz => hF1 z hz)
    (x := circleMap (c : ℂ) ρ (Real.pi - α)) (y := p2)
    ⟨mU _ ⟨by linarith, le_rfl⟩, mL _ ⟨le_rfl, by linarith⟩⟩ ⟨hp2.1, hp2.2⟩
  have j3 := quad_const (h := h) oL oD convL convD (fun z hz => hF1 z hz) (fun z hz => hF4 z hz)
    (x := circleMap (c : ℂ) ρ (Real.pi + α)) (y := p3)
    ⟨mL _ ⟨by linarith, le_rfl⟩, mD _ ⟨le_rfl, by linarith⟩⟩ ⟨hp3.1, hp3.2⟩
  have j4 := quad_const (h := h) oD oR convD convR (fun z hz => hF4 z hz) (fun z hz => hF3 z hz)
    (x := circleMap (c : ℂ) ρ (-α)) (y := p0)
    ⟨by
      have := mD (2 * Real.pi - α) ⟨by linarith, le_rfl⟩
      rwa [hq0] at this, mR _ ⟨le_rfl, by linarith⟩⟩ ⟨hp0.1, hp0.2⟩
  linear_combination j1 + j2 + j3 + j4


/-! ## K2b: the BBP contour Γ* integrates to the same chain constant -/

theorem lin_integral_prim {F h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) (hc : ContinuousOn h U) (p d : ℂ) (s t : ℝ) (hst : s ≤ t)
    (hmem : ∀ τ ∈ Icc s t, p + (τ : ℂ) * d ∈ U) :
    ∫ τ in s..t, h (p + (τ : ℂ) * d) * d = F (p + (t : ℂ) * d) - F (p + (s : ℂ) * d) := by
  have hγ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => p + (τ : ℂ) * d) d τ := by
    intro τ
    have := ((hasDerivAt_id τ).ofReal_comp).mul_const d
    simpa using this.const_add p
  exact path_integral_prim hU hF hc (fun τ : ℝ => p + (τ : ℂ) * d) (fun _ => d) s t hst hγ
    continuous_const hmem

theorem lin_re_im (p τ : ℝ) (d : ℂ) : ((p : ℂ) + (τ : ℂ) * d).re = p + τ * d.re ∧
    ((p : ℂ) + (τ : ℂ) * d).im = τ * d.im := by
  constructor <;> simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]

theorem omega_re_im : (exp (((Real.pi / 3 : ℝ) : ℂ) * I)).re = 1 / 2 ∧
    (exp (((Real.pi / 3 : ℝ) : ℂ) * I)).im = Real.sqrt 3 / 2 ∧
    (exp (((-Real.pi / 3 : ℝ) : ℂ) * I)).re = 1 / 2 ∧
    (exp (((-Real.pi / 3 : ℝ) : ℂ) * I)).im = -(Real.sqrt 3 / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, Real.sin_pi_div_three]
  · rw [exp_ofReal_mul_I_re, neg_div, Real.cos_neg, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, neg_div, Real.sin_neg, Real.sin_pi_div_three]

set_option maxHeartbeats 2000000 in
/-- **K2b.** The closed BBP contour `Γ*` (vertical side at `Re = pc + ℓ/2 + R`, horizontal sides,
`Γ₁` pieces at angles `±π/3` from `pc`, connectors at height `±δ sin(π/3)`, and the rays at `±π/3`
from the real vertex `v`) integrates to the chain constant. -/
theorem polygon_chain {h F1 F2 F3 F4 : ℂ → ℂ} {a b : ℝ}
    (hcont : ContinuousOn h {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re})
    (hF1 : ∀ z : ℂ, z.re < a → HasDerivAt F1 (h z) z)
    (hF2 : ∀ z : ℂ, 0 < z.im → HasDerivAt F2 (h z) z)
    (hF3 : ∀ z : ℂ, b < z.re → HasDerivAt F3 (h z) z)
    (hF4 : ∀ z : ℂ, z.im < 0 → HasDerivAt F4 (h z) z)
    (pc v δ ℓ R : ℝ) (hv : v < a) (hvpc : v ≤ pc) (hδ : 0 < δ) (hδℓ : δ ≤ ℓ) (hR : 0 ≤ R)
    (hX : b < pc + ℓ / 2 + R) :
    ∃ p2 p3 : ℂ, (0 < p2.im ∧ p2.re < a) ∧ (p3.re < a ∧ p3.im < 0) ∧
    (∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((pc + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R, h ((pc : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))
      - (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(pc - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(pc - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((pc : ℂ) + (ℓ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))
      = (F3 (((pc + ℓ / 2 + R : ℝ) : ℂ) + ((ℓ * (Real.sqrt 3 / 2) : ℝ) : ℂ) * I) -
          F2 (((pc + ℓ / 2 + R : ℝ) : ℂ) + ((ℓ * (Real.sqrt 3 / 2) : ℝ) : ℂ) * I)) +
        (F2 p2 - F1 p2) + (F1 p3 - F4 p3) +
        (F4 (((pc + ℓ / 2 + R : ℝ) : ℂ) + ((-(ℓ * (Real.sqrt 3 / 2)) : ℝ) : ℂ) * I) -
          F3 (((pc + ℓ / 2 + R : ℝ) : ℂ) + ((-(ℓ * (Real.sqrt 3 / 2)) : ℝ) : ℂ) * I)) := by
  obtain ⟨hωr, hωi, hωbr, hωbi⟩ := omega_re_im
  set ω : ℂ := exp (((Real.pi / 3 : ℝ) : ℂ) * I) with hω
  set ωb : ℂ := exp (((-Real.pi / 3 : ℝ) : ℂ) * I) with hωb
  have hs3 : 0 < Real.sqrt 3 / 2 := by have := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3); linarith
  have hℓ : 0 < ℓ := lt_of_lt_of_le hδ hδℓ
  have hωeq : ω = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hωr, hωi]
  have hωbeq : ωb = ((1 / 2 : ℝ) : ℂ) + ((-(Real.sqrt 3 / 2) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hωbr, hωbi]
  set t1 : ℝ := min δ (a - v) with ht1
  have ht1p : 0 < t1 := lt_min hδ (by linarith)
  have ht1δ : t1 ≤ δ := min_le_left _ _
  have ht1a : t1 ≤ a - v := min_le_right _ _
  set Y : ℝ := ℓ * (Real.sqrt 3 / 2) with hY
  have hY0 : 0 < Y := mul_pos hℓ hs3
  set X : ℝ := pc + ℓ / 2 + R with hXd
  -- domains
  have oL : IsOpen {z : ℂ | z.re < a} := isOpen_lt Complex.continuous_re continuous_const
  have oU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have oR : IsOpen {z : ℂ | b < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have oD : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have cL : ContinuousOn h {z : ℂ | z.re < a} := hcont.mono (fun z hz => Or.inr (Or.inl hz))
  have cU : ContinuousOn h {z : ℂ | 0 < z.im} := hcont.mono (fun z hz => Or.inl (ne_of_gt hz))
  have cR : ContinuousOn h {z : ℂ | b < z.re} := hcont.mono (fun z hz => Or.inr (Or.inr hz))
  have cD : ContinuousOn h {z : ℂ | z.im < 0} := hcont.mono (fun z hz => Or.inl (ne_of_lt hz))
  have gF1 : ∀ z ∈ {z : ℂ | z.re < a}, HasDerivAt F1 (h z) z := fun z hz => hF1 z hz
  have gF2 : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt F2 (h z) z := fun z hz => hF2 z hz
  have gF3 : ∀ z ∈ {z : ℂ | b < z.re}, HasDerivAt F3 (h z) z := fun z hz => hF3 z hz
  have gF4 : ∀ z ∈ {z : ℂ | z.im < 0}, HasDerivAt F4 (h z) z := fun z hz => hF4 z hz
  -- pieces
  have Pv := lin_integral_prim oR gF3 cR ((X : ℝ) : ℂ) I (-Y) Y (by linarith) (fun τ _ => by
    show b < ((X : ℂ) + (τ : ℂ) * I).re
    simp; linarith)
  have P2u := lin_integral_prim oU gF2 cU ((pc : ℂ) + (ℓ : ℂ) * ω) 1 0 R hR (fun τ _ => by
    show 0 < ((pc : ℂ) + (ℓ : ℂ) * ω + (τ : ℂ) * 1).im
    have := (lin_re_im pc ℓ ω).2
    rw [mul_one, Complex.add_im, this, Complex.ofReal_im, add_zero, hωi]; exact mul_pos hℓ hs3)
  have P1u := lin_integral_prim oU gF2 cU (pc : ℂ) ω δ ℓ hδℓ (fun τ hτ => by
    show 0 < ((pc : ℂ) + (τ : ℂ) * ω).im
    rw [(lin_re_im pc τ ω).2, hωi]; exact mul_pos (by linarith [hτ.1]) hs3)
  have PCu := lin_integral_prim oU gF2 cU ((v : ℂ) + (δ : ℂ) * ω) 1 0 (pc - v) (by linarith)
    (fun τ _ => by
      show 0 < ((v : ℂ) + (δ : ℂ) * ω + (τ : ℂ) * 1).im
      have := (lin_re_im v δ ω).2
      rw [mul_one, Complex.add_im, this, Complex.ofReal_im, add_zero, hωi]; exact mul_pos hδ hs3)
  have PRu1 := lin_integral_prim oU gF2 cU (v : ℂ) ω t1 δ ht1δ (fun τ hτ => by
    show 0 < ((v : ℂ) + (τ : ℂ) * ω).im
    rw [(lin_re_im v τ ω).2, hωi]; exact mul_pos (by linarith [hτ.1]) hs3)
  have PRu0 := lin_integral_prim oL gF1 cL (v : ℂ) ω 0 t1 ht1p.le (fun τ hτ => by
    show ((v : ℂ) + (τ : ℂ) * ω).re < a
    rw [(lin_re_im v τ ω).1, hωr]; linarith [hτ.2])
  have PRd0 := lin_integral_prim oL gF1 cL (v : ℂ) ωb 0 t1 ht1p.le (fun τ hτ => by
    show ((v : ℂ) + (τ : ℂ) * ωb).re < a
    rw [(lin_re_im v τ ωb).1, hωbr]; linarith [hτ.2])
  have PRd1 := lin_integral_prim oD gF4 cD (v : ℂ) ωb t1 δ ht1δ (fun τ hτ => by
    show ((v : ℂ) + (τ : ℂ) * ωb).im < 0
    rw [(lin_re_im v τ ωb).2, hωbi]
    have := mul_pos (by linarith [hτ.1] : (0 : ℝ) < τ) hs3
    linarith)
  have PCd := lin_integral_prim oD gF4 cD ((v : ℂ) + (δ : ℂ) * ωb) 1 0 (pc - v) (by linarith)
    (fun τ _ => by
      show ((v : ℂ) + (δ : ℂ) * ωb + (τ : ℂ) * 1).im < 0
      have := (lin_re_im v δ ωb).2
      rw [mul_one, Complex.add_im, this, Complex.ofReal_im, add_zero, hωbi]
      have := mul_pos hδ hs3
      linarith)
  have P1d := lin_integral_prim oD gF4 cD (pc : ℂ) ωb δ ℓ hδℓ (fun τ hτ => by
    show ((pc : ℂ) + (τ : ℂ) * ωb).im < 0
    rw [(lin_re_im pc τ ωb).2, hωbi]
    have := mul_pos (by linarith [hτ.1] : (0 : ℝ) < τ) hs3
    linarith)
  have P2d := lin_integral_prim oD gF4 cD ((pc : ℂ) + (ℓ : ℂ) * ωb) 1 0 R hR (fun τ _ => by
    show ((pc : ℂ) + (ℓ : ℂ) * ωb + (τ : ℂ) * 1).im < 0
    have := (lin_re_im pc ℓ ωb).2
    rw [mul_one, Complex.add_im, this, Complex.ofReal_im, add_zero, hωbi]
    have := mul_pos hℓ hs3
    linarith)
  simp only [mul_one, Complex.ofReal_zero, zero_mul, add_zero] at P2u PCu PCd P2d PRu0 PRd0
  -- split the two near rays at t1
  have rayc : ∀ d : ℂ, d.re = 1 / 2 → d.im ≠ 0 →
      ContinuousOn (fun τ : ℝ => h ((v : ℂ) + (τ : ℂ) * d) * d) (Icc 0 δ) := by
    intro d hdr hdi
    refine (hcont.comp (by fun_prop : Continuous fun τ : ℝ => (v : ℂ) + (τ : ℂ) * d).continuousOn
      (fun τ hτ => ?_)).mul continuousOn_const
    rcases eq_or_lt_of_le hτ.1 with h0 | h0
    · right; left
      show ((v : ℂ) + (τ : ℂ) * d).re < a
      rw [(lin_re_im v τ d).1, ← h0]; linarith
    · left
      show ((v : ℂ) + (τ : ℂ) * d).im ≠ 0
      rw [(lin_re_im v τ d).2]; exact mul_ne_zero h0.ne' hdi
  have cu := rayc ω hωr (by rw [hωi]; exact hs3.ne')
  have cd := rayc ωb hωbr (by rw [hωbi]; exact (neg_neg_of_pos hs3).ne)
  have ii : ∀ (f : ℝ → ℂ), ContinuousOn f (Icc 0 δ) → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ δ →
      IntervalIntegrable f MeasureTheory.volume s t := by
    intro f hf s t h0 h1 h2
    refine (hf.mono ?_).intervalIntegrable
    rw [uIcc_of_le h1]
    exact Icc_subset_Icc h0 h2
  have Su := intervalIntegral.integral_add_adjacent_intervals
    (ii _ cu 0 t1 le_rfl ht1p.le ht1δ) (ii _ cu t1 δ ht1p.le ht1δ le_rfl)
  have Sd := intervalIntegral.integral_add_adjacent_intervals
    (ii _ cd 0 t1 le_rfl ht1p.le ht1δ) (ii _ cd t1 δ ht1p.le ht1δ le_rfl)
  -- corner identities
  have e1 : (pc : ℂ) + (ℓ : ℂ) * ω + (R : ℂ) = (X : ℂ) + (Y : ℂ) * I := by
    rw [hωeq, hXd, hY]; push_cast; ring
  have e0 : (pc : ℂ) + (ℓ : ℂ) * ωb + (R : ℂ) = (X : ℂ) + ((-Y : ℝ) : ℂ) * I := by
    rw [hωbeq, hXd, hY]; push_cast; ring
  have ecu : (v : ℂ) + (δ : ℂ) * ω + ((pc - v : ℝ) : ℂ) = (pc : ℂ) + (δ : ℂ) * ω := by
    push_cast; ring
  have ecd : (v : ℂ) + (δ : ℂ) * ωb + ((pc - v : ℝ) : ℂ) = (pc : ℂ) + (δ : ℂ) * ωb := by
    push_cast; ring
  rw [e1] at P2u
  rw [e0] at P2d
  rw [ecu] at PCu
  rw [ecd] at PCd
  refine ⟨(v : ℂ) + (t1 : ℂ) * ω, (v : ℂ) + (t1 : ℂ) * ωb, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [(lin_re_im v t1 ω).2, hωi]; exact mul_pos ht1p hs3
  · rw [(lin_re_im v t1 ω).1, hωr]; linarith
  · rw [(lin_re_im v t1 ωb).1, hωbr]; linarith
  · rw [(lin_re_im v t1 ωb).2, hωbi]; have := mul_pos ht1p hs3; linarith
  · rw [← Su, ← Sd, Pv, P2u, P1u, PCu, PRu1, PRu0, PRd0, PRd1, PCd, P1d, P2d]
    ring


set_option maxHeartbeats 1000000 in
/-- **K2 (combined).** Circle integral = integral over the BBP contour `Γ*`, for `h` holomorphic
off the real segment `[a, b]`. -/
theorem circle_eq_polygon {h : ℂ → ℂ} {a b c ρ : ℝ} (hab : a ≤ b) (ha : c - ρ < a) (hb : b < c + ρ)
    (hd : DifferentiableOn ℂ h {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re})
    (pc v δ ℓ R : ℝ) (hv : v < a) (hvpc : v ≤ pc) (hδ : 0 < δ) (hδℓ : δ ≤ ℓ) (hR : 0 ≤ R)
    (hX : b < pc + ℓ / 2 + R) :
    (∮ z in C((c : ℂ), ρ), h z) =
    (∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((pc + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R, h ((pc : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))
      - (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(pc - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(pc - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((pc : ℂ) + (ℓ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) := by
  obtain ⟨F1, F2, F3, F4, hF1, hF2, hF3, hF4⟩ := quad_prims hd
  obtain ⟨p2, p3, hp2, hp3, hpoly⟩ := polygon_chain hd.continuousOn hF1 hF2 hF3 hF4 pc v δ ℓ R
    hv hvpc hδ hδℓ hR hX
  have hs3 : 0 < Real.sqrt 3 / 2 := by have := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3); linarith
  have hY : 0 < ℓ * (Real.sqrt 3 / 2) := mul_pos (lt_of_lt_of_le hδ hδℓ) hs3
  rw [hpoly]
  refine circle_chain hab ha hb hd.continuousOn hF1 hF2 hF3 hF4 _ _ p2 p3 ⟨?_, ?_⟩ ⟨?_, ?_⟩ hp2 hp3
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith


/-! ## K3: the BBP contour Σ* (pole at 0 only) -/

theorem omega2_re_im : (exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)).re = -(1 / 2) ∧
    (exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)).im = Real.sqrt 3 / 2 ∧
    (exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)).re = -(1 / 2) ∧
    (exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)).im = -(Real.sqrt 3 / 2) := by
  have e : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  have e' : -2 * Real.pi / 3 = -(Real.pi - Real.pi / 3) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exp_ofReal_mul_I_re, e, Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, e, Real.sin_pi_sub, Real.sin_pi_div_three]
  · rw [exp_ofReal_mul_I_re, e', Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [exp_ofReal_mul_I_im, e', Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem lin_integral_prim_neg {F h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ z ∈ U, HasDerivAt F (h z) z) (hc : ContinuousOn h U) (p : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hmem : ∀ τ ∈ Icc 0 R, p + (τ : ℂ) * (-1) ∈ U) :
    ∫ x in (0 : ℝ)..R, h (p - (x : ℂ)) = F p - F (p - (R : ℂ)) := by
  have P := lin_integral_prim hU hF hc p (-1) 0 R hR hmem
  have e : ∫ x in (0 : ℝ)..R, h (p - (x : ℂ)) =
      -∫ x in (0 : ℝ)..R, h (p + (x : ℂ) * (-1)) * (-1) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [show p + (x : ℂ) * (-1) = p - (x : ℂ) by ring]
    ring
  rw [e, P, show p + (R : ℂ) * (-1) = p - (R : ℂ) by ring]
  simp

set_option maxHeartbeats 2000000 in
/-- **K3b.** The closed BBP contour `Σ*` around `0`: rays at `±2π/3` from the real vertex `w₀ > 0`,
connectors, `Σ₁` pieces from `pc`, horizontal `Σ₂` pieces and the vertical side at
`Re = pc - ℓ/2 - R < 0`, integrates to the chain constant for the segment `[0, 0]`. -/
theorem polygonJ_chain {h F1 F2 F3 F4 : ℂ → ℂ}
    (hcont : ContinuousOn h {z : ℂ | z.im ≠ 0 ∨ z.re < 0 ∨ 0 < z.re})
    (hF1 : ∀ z : ℂ, z.re < 0 → HasDerivAt F1 (h z) z)
    (hF2 : ∀ z : ℂ, 0 < z.im → HasDerivAt F2 (h z) z)
    (hF3 : ∀ z : ℂ, 0 < z.re → HasDerivAt F3 (h z) z)
    (hF4 : ∀ z : ℂ, z.im < 0 → HasDerivAt F4 (h z) z)
    (pc w0 δ ℓ R : ℝ) (hw0 : 0 < w0) (hwpc : w0 ≤ pc) (hδ : 0 < δ) (hδℓ : δ ≤ ℓ) (hR : 0 ≤ R)
    (hX : pc - ℓ / 2 - R < 0) :
    ∃ p0 p1 : ℂ, (p0.im < 0 ∧ 0 < p0.re) ∧ (0 < p1.re ∧ 0 < p1.im) ∧
    -(∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((pc - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R,
          h ((pc : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)))
      + (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(pc - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(pc - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((pc : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)))
      = (F3 p1 - F2 p1) +
        (F2 (((pc - ℓ / 2 - R : ℝ) : ℂ) + ((ℓ * (Real.sqrt 3 / 2) : ℝ) : ℂ) * I) -
          F1 (((pc - ℓ / 2 - R : ℝ) : ℂ) + ((ℓ * (Real.sqrt 3 / 2) : ℝ) : ℂ) * I)) +
        (F1 (((pc - ℓ / 2 - R : ℝ) : ℂ) + ((-(ℓ * (Real.sqrt 3 / 2)) : ℝ) : ℂ) * I) -
          F4 (((pc - ℓ / 2 - R : ℝ) : ℂ) + ((-(ℓ * (Real.sqrt 3 / 2)) : ℝ) : ℂ) * I)) +
        (F4 p0 - F3 p0) := by
  obtain ⟨hωr, hωi, hωbr, hωbi⟩ := omega2_re_im
  set ω : ℂ := exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) with hω
  set ωb : ℂ := exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) with hωb
  have hs3 : 0 < Real.sqrt 3 / 2 := by have := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3); linarith
  have hℓ : 0 < ℓ := lt_of_lt_of_le hδ hδℓ
  have hωeq : ω = ((-(1 / 2) : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hωr, hωi]
  have hωbeq : ωb = ((-(1 / 2) : ℝ) : ℂ) + ((-(Real.sqrt 3 / 2) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hωbr, hωbi]
  set t1 : ℝ := min δ w0 with ht1
  have ht1p : 0 < t1 := lt_min hδ hw0
  have ht1δ : t1 ≤ δ := min_le_left _ _
  have ht1a : t1 ≤ w0 := min_le_right _ _
  set Y : ℝ := ℓ * (Real.sqrt 3 / 2) with hY
  have hY0 : 0 < Y := mul_pos hℓ hs3
  set X : ℝ := pc - ℓ / 2 - R with hXd
  have oL : IsOpen {z : ℂ | z.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have oU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have oR : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have oD : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have cL : ContinuousOn h {z : ℂ | z.re < 0} := hcont.mono (fun z hz => Or.inr (Or.inl hz))
  have cU : ContinuousOn h {z : ℂ | 0 < z.im} := hcont.mono (fun z hz => Or.inl (ne_of_gt hz))
  have cR : ContinuousOn h {z : ℂ | 0 < z.re} := hcont.mono (fun z hz => Or.inr (Or.inr hz))
  have cD : ContinuousOn h {z : ℂ | z.im < 0} := hcont.mono (fun z hz => Or.inl (ne_of_lt hz))
  have gF1 : ∀ z ∈ {z : ℂ | z.re < 0}, HasDerivAt F1 (h z) z := fun z hz => hF1 z hz
  have gF2 : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt F2 (h z) z := fun z hz => hF2 z hz
  have gF3 : ∀ z ∈ {z : ℂ | 0 < z.re}, HasDerivAt F3 (h z) z := fun z hz => hF3 z hz
  have gF4 : ∀ z ∈ {z : ℂ | z.im < 0}, HasDerivAt F4 (h z) z := fun z hz => hF4 z hz
  have Pv := lin_integral_prim oL gF1 cL ((X : ℝ) : ℂ) I (-Y) Y (by linarith) (fun τ _ => by
    show ((X : ℂ) + (τ : ℂ) * I).re < 0
    simp; linarith)
  have P2u := lin_integral_prim_neg oU gF2 cU ((pc : ℂ) + (ℓ : ℂ) * ω) R hR (fun τ _ => by
    show 0 < ((pc : ℂ) + (ℓ : ℂ) * ω + (τ : ℂ) * (-1)).im
    have := (lin_re_im pc ℓ ω).2
    rw [Complex.add_im, this, hωi]
    simp only [mul_neg, mul_one, Complex.neg_im, Complex.ofReal_im, neg_zero, add_zero]
    exact mul_pos hℓ hs3)
  have P1u := lin_integral_prim oU gF2 cU (pc : ℂ) ω δ ℓ hδℓ (fun τ hτ => by
    show 0 < ((pc : ℂ) + (τ : ℂ) * ω).im
    rw [(lin_re_im pc τ ω).2, hωi]; exact mul_pos (by linarith [hτ.1]) hs3)
  have PCu := lin_integral_prim oU gF2 cU ((w0 : ℂ) + (δ : ℂ) * ω) 1 0 (pc - w0) (by linarith)
    (fun τ _ => by
      show 0 < ((w0 : ℂ) + (δ : ℂ) * ω + (τ : ℂ) * 1).im
      have := (lin_re_im w0 δ ω).2
      rw [mul_one, Complex.add_im, this, Complex.ofReal_im, add_zero, hωi]; exact mul_pos hδ hs3)
  have PRu1 := lin_integral_prim oU gF2 cU (w0 : ℂ) ω t1 δ ht1δ (fun τ hτ => by
    show 0 < ((w0 : ℂ) + (τ : ℂ) * ω).im
    rw [(lin_re_im w0 τ ω).2, hωi]; exact mul_pos (by linarith [hτ.1]) hs3)
  have PRu0 := lin_integral_prim oR gF3 cR (w0 : ℂ) ω 0 t1 ht1p.le (fun τ hτ => by
    show 0 < ((w0 : ℂ) + (τ : ℂ) * ω).re
    rw [(lin_re_im w0 τ ω).1, hωr]; linarith [hτ.2])
  have PRd0 := lin_integral_prim oR gF3 cR (w0 : ℂ) ωb 0 t1 ht1p.le (fun τ hτ => by
    show 0 < ((w0 : ℂ) + (τ : ℂ) * ωb).re
    rw [(lin_re_im w0 τ ωb).1, hωbr]; linarith [hτ.2])
  have PRd1 := lin_integral_prim oD gF4 cD (w0 : ℂ) ωb t1 δ ht1δ (fun τ hτ => by
    show ((w0 : ℂ) + (τ : ℂ) * ωb).im < 0
    rw [(lin_re_im w0 τ ωb).2, hωbi]
    have := mul_pos (by linarith [hτ.1] : (0 : ℝ) < τ) hs3
    linarith)
  have PCd := lin_integral_prim oD gF4 cD ((w0 : ℂ) + (δ : ℂ) * ωb) 1 0 (pc - w0) (by linarith)
    (fun τ _ => by
      show ((w0 : ℂ) + (δ : ℂ) * ωb + (τ : ℂ) * 1).im < 0
      have := (lin_re_im w0 δ ωb).2
      rw [mul_one, Complex.add_im, this, Complex.ofReal_im, add_zero, hωbi]
      have := mul_pos hδ hs3
      linarith)
  have P1d := lin_integral_prim oD gF4 cD (pc : ℂ) ωb δ ℓ hδℓ (fun τ hτ => by
    show ((pc : ℂ) + (τ : ℂ) * ωb).im < 0
    rw [(lin_re_im pc τ ωb).2, hωbi]
    have := mul_pos (by linarith [hτ.1] : (0 : ℝ) < τ) hs3
    linarith)
  have P2d := lin_integral_prim_neg oD gF4 cD ((pc : ℂ) + (ℓ : ℂ) * ωb) R hR (fun τ _ => by
    show ((pc : ℂ) + (ℓ : ℂ) * ωb + (τ : ℂ) * (-1)).im < 0
    have := (lin_re_im pc ℓ ωb).2
    rw [Complex.add_im, this, hωbi]
    simp only [mul_neg, mul_one, Complex.neg_im, Complex.ofReal_im, neg_zero, add_zero]
    have := mul_pos hℓ hs3
    linarith)
  simp only [mul_one, Complex.ofReal_zero, zero_mul, add_zero] at PCu PCd PRu0 PRd0
  have rayc : ∀ d : ℂ, d.re = -(1 / 2) → d.im ≠ 0 →
      ContinuousOn (fun τ : ℝ => h ((w0 : ℂ) + (τ : ℂ) * d) * d) (Icc 0 δ) := by
    intro d hdr hdi
    refine (hcont.comp (by fun_prop : Continuous fun τ : ℝ => (w0 : ℂ) + (τ : ℂ) * d).continuousOn
      (fun τ hτ => ?_)).mul continuousOn_const
    rcases eq_or_lt_of_le hτ.1 with h0 | h0
    · right; right
      show 0 < ((w0 : ℂ) + (τ : ℂ) * d).re
      rw [(lin_re_im w0 τ d).1, ← h0]; linarith
    · left
      show ((w0 : ℂ) + (τ : ℂ) * d).im ≠ 0
      rw [(lin_re_im w0 τ d).2]; exact mul_ne_zero h0.ne' hdi
  have cu := rayc ω hωr (by rw [hωi]; exact hs3.ne')
  have cd := rayc ωb hωbr (by rw [hωbi]; exact (neg_neg_of_pos hs3).ne)
  have ii : ∀ (f : ℝ → ℂ), ContinuousOn f (Icc 0 δ) → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ δ →
      IntervalIntegrable f MeasureTheory.volume s t := by
    intro f hf s t h0 h1 h2
    refine (hf.mono ?_).intervalIntegrable
    rw [uIcc_of_le h1]
    exact Icc_subset_Icc h0 h2
  have Su := intervalIntegral.integral_add_adjacent_intervals
    (ii _ cu 0 t1 le_rfl ht1p.le ht1δ) (ii _ cu t1 δ ht1p.le ht1δ le_rfl)
  have Sd := intervalIntegral.integral_add_adjacent_intervals
    (ii _ cd 0 t1 le_rfl ht1p.le ht1δ) (ii _ cd t1 δ ht1p.le ht1δ le_rfl)
  have e1 : (pc : ℂ) + (ℓ : ℂ) * ω - (R : ℂ) = (X : ℂ) + (Y : ℂ) * I := by
    rw [hωeq, hXd, hY]; push_cast; ring
  have e0 : (pc : ℂ) + (ℓ : ℂ) * ωb - (R : ℂ) = (X : ℂ) + ((-Y : ℝ) : ℂ) * I := by
    rw [hωbeq, hXd, hY]; push_cast; ring
  have ecu : (w0 : ℂ) + (δ : ℂ) * ω + ((pc - w0 : ℝ) : ℂ) = (pc : ℂ) + (δ : ℂ) * ω := by
    push_cast; ring
  have ecd : (w0 : ℂ) + (δ : ℂ) * ωb + ((pc - w0 : ℝ) : ℂ) = (pc : ℂ) + (δ : ℂ) * ωb := by
    push_cast; ring
  rw [e1] at P2u
  rw [e0] at P2d
  rw [ecu] at PCu
  rw [ecd] at PCd
  refine ⟨(w0 : ℂ) + (t1 : ℂ) * ωb, (w0 : ℂ) + (t1 : ℂ) * ω, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [(lin_re_im w0 t1 ωb).2, hωbi]; have := mul_pos ht1p hs3; linarith
  · rw [(lin_re_im w0 t1 ωb).1, hωbr]; linarith
  · rw [(lin_re_im w0 t1 ω).1, hωr]; linarith
  · rw [(lin_re_im w0 t1 ω).2, hωi]; exact mul_pos ht1p hs3
  · rw [← Su, ← Sd, Pv, P2u, P1u, PCu, PRu1, PRu0, PRd0, PRd1, PCd, P1d, P2d]
    ring


set_option maxHeartbeats 1000000 in
/-- **K3 (combined).** Circle around `0` = integral over the BBP contour `Σ*`, for `h` holomorphic
off `0`. -/
theorem circle_eq_polygonJ {h : ℂ → ℂ} {c ρ : ℝ} (ha : c - ρ < 0) (hb : 0 < c + ρ)
    (hd : DifferentiableOn ℂ h {z : ℂ | z.im ≠ 0 ∨ z.re < 0 ∨ 0 < z.re})
    (pc w0 δ ℓ R : ℝ) (hw0 : 0 < w0) (hwpc : w0 ≤ pc) (hδ : 0 < δ) (hδℓ : δ ≤ ℓ) (hR : 0 ≤ R)
    (hX : pc - ℓ / 2 - R < 0) :
    (∮ z in C((c : ℂ), ρ), h z) =
    -(∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((pc - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R,
          h ((pc : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)))
      + (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(pc - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(pc - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in δ..ℓ, h ((pc : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((pc : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))) := by
  obtain ⟨F1, F2, F3, F4, hF1, hF2, hF3, hF4⟩ := quad_prims hd
  obtain ⟨p0, p1, hp0, hp1, hpoly⟩ := polygonJ_chain hd.continuousOn hF1 hF2 hF3 hF4 pc w0 δ ℓ R
    hw0 hwpc hδ hδℓ hR hX
  have hs3 : 0 < Real.sqrt 3 / 2 := by have := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3); linarith
  have hY : 0 < ℓ * (Real.sqrt 3 / 2) := mul_pos (lt_of_lt_of_le hδ hδℓ) hs3
  rw [hpoly]
  refine circle_chain le_rfl ha hb hd.continuousOn hF1 hF2 hF3 hF4 p0 p1 _ _ hp0 hp1
    ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith

end P31

open Complex MeasureTheory in
theorem solution :
    ∀ (h : ℂ → ℂ) (a b c ρ : ℝ), a ≤ b → c - ρ < a → b < c + ρ →
    DifferentiableOn ℂ h {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re} →
    ∀ (p v δ ℓ R : ℝ), v < a → v ≤ p → 0 < δ → δ ≤ ℓ → 0 ≤ R → b < p + ℓ / 2 + R →
    (∮ z in C((c : ℂ), ρ), h z) =
    (∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((p + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R, h ((p : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))
      - (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(p - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(p - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((p : ℂ) + (ℓ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) := by
  intro h a b c ρ
  exact P31.circle_eq_polygon
