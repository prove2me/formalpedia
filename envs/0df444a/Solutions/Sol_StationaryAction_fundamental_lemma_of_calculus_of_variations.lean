-- Prove2me | solution 1 for StationaryAction.fundamental_lemma_of_calculus_of_variations
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:04:58.952482+00:00
-- url     : https://prove2.me/submissions/c6594470-016e-4b82-a944-ad1c54382721

import Definitions.Def_StationaryActionCore

open StationaryAction

/-! ## Helper lemmas -/

theorem W4b_StationaryAction_hsq (w : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * w) w := by
  simpa using hasDerivAt_pow 2 w

theorem W4b_StationaryAction_hsq2 (d x : ℝ) :
    HasDerivAt (fun s : ℝ => (d - s) ^ 2) (-(2 * (d - x))) x := by
  exact ((W4b_StationaryAction_hsq (d - x)).comp x ((hasDerivAt_id' x).const_sub d)).congr_deriv
    (by ring)

theorem W4b_StationaryAction_dd {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) : ContDiff ℝ 1 (deriv q) := by
  have h : ContDiff ℝ (1 + 1) q := by rwa [one_add_one_eq_two]
  exact (contDiff_succ_iff_deriv.mp h).2.2

theorem W4b_StationaryAction_path {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y) :
    ContDiff ℝ 1 (fun t => (y t, deriv y t, t)) :=
  (hy.of_le one_le_two).prodMk ((W4b_StationaryAction_dd hy).prodMk contDiff_id)

theorem W4b_StationaryAction_pY (f : ℝ → ℝ → ℝ → ℝ) (F : ℝ × ℝ × ℝ → ℝ)
    (hFf : ∀ u v x, f u v x = F (u, v, x)) (hFd : Differentiable ℝ F) (u v x : ℝ) :
    partialY f u v x = fderiv ℝ F (u, v, x) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
  have hg : HasDerivAt (fun w : ℝ => (w, v, x)) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) u :=
    (hasDerivAt_id' u).prodMk ((hasDerivAt_const u v).prodMk (hasDerivAt_const u x))
  have h := (hFd (u, v, x)).hasFDerivAt.comp_hasDerivAt u hg
  unfold partialY
  simp only [hFf]
  exact h.deriv

theorem W4b_StationaryAction_pV (f : ℝ → ℝ → ℝ → ℝ) (F : ℝ × ℝ × ℝ → ℝ)
    (hFf : ∀ u v x, f u v x = F (u, v, x)) (hFd : Differentiable ℝ F) (u v x : ℝ) :
    partialV f u v x = fderiv ℝ F (u, v, x) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) := by
  have hg : HasDerivAt (fun w : ℝ => (u, w, x)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) v :=
    (hasDerivAt_const v u).prodMk ((hasDerivAt_id' v).prodMk (hasDerivAt_const v x))
  have h := (hFd (u, v, x)).hasFDerivAt.comp_hasDerivAt v hg
  unfold partialV
  simp only [hFf]
  exact h.deriv

theorem W4b_StationaryAction_alongC1 (F : ℝ × ℝ × ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (y : ℝ → ℝ) (hy : ContDiff ℝ 2 y) (w : ℝ × ℝ × ℝ) :
    ContDiff ℝ 1 (fun t => fderiv ℝ F (y t, deriv y t, t) w) :=
  ((hF.fderiv_right (le_of_eq one_add_one_eq_two)).comp
    (W4b_StationaryAction_path hy)).clm_apply contDiff_const

theorem W4b_StationaryAction_pVC1 (f : ℝ → ℝ → ℝ → ℝ) (F : ℝ × ℝ × ℝ → ℝ)
    (hFf : ∀ u v x, f u v x = F (u, v, x)) (hF : ContDiff ℝ 2 F)
    (y : ℝ → ℝ) (hy : ContDiff ℝ 2 y) :
    ContDiff ℝ 1 (fun t => partialV f (y t) (deriv y t) t) := by
  have e : (fun t => partialV f (y t) (deriv y t) t) =
      fun t => fderiv ℝ F (y t, deriv y t, t) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) :=
    funext fun t => W4b_StationaryAction_pV f F hFf (hF.differentiable (by simp)) _ _ _
  rw [e]
  exact W4b_StationaryAction_alongC1 F hF y hy _

theorem W4b_StationaryAction_pYC1 (f : ℝ → ℝ → ℝ → ℝ) (F : ℝ × ℝ × ℝ → ℝ)
    (hFf : ∀ u v x, f u v x = F (u, v, x)) (hF : ContDiff ℝ 2 F)
    (y : ℝ → ℝ) (hy : ContDiff ℝ 2 y) :
    ContDiff ℝ 1 (fun t => partialY f (y t) (deriv y t) t) := by
  have e : (fun t => partialY f (y t) (deriv y t) t) =
      fun t => fderiv ℝ F (y t, deriv y t, t) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) :=
    funext fun t => W4b_StationaryAction_pY f F hFf (hF.differentiable (by simp)) _ _ _
  rw [e]
  exact W4b_StationaryAction_alongC1 F hF y hy _

theorem W4b_StationaryAction_const_on (G : ℝ → ℝ) (x₁ x₂ : ℝ) (hd : Differentiable ℝ G)
    (h0 : ∀ x ∈ Set.Icc x₁ x₂, deriv G x = 0) : ∀ x ∈ Set.Icc x₁ x₂, G x = G x₁ := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [h]
  · obtain ⟨c, hc, hcd⟩ :=
      exists_deriv_eq_slope G h hd.continuous.continuousOn hd.differentiableOn
    rw [h0 c ⟨hc.1.le, hc.2.le.trans hx.2⟩, eq_comm, div_eq_zero_iff] at hcd
    rcases hcd with h' | h'
    · linarith
    · exfalso; linarith

/-! ## Elementary extremum problems -/

theorem W4b_StationaryAction_fermat_max_product (b : ℝ) :
    IsMaxOn (fun a : ℝ => a * (b - a)) Set.univ (b / 2) := by
  rw [isMaxOn_iff]
  intro x _
  show x * (b - x) ≤ b / 2 * (b - b / 2)
  nlinarith [sq_nonneg (x - b / 2)]

theorem W4b_StationaryAction_galileo_law_of_chords
    (g D phi t : ℝ) (hg : 0 < g) (hD : 0 < D)
    (hphi : phi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (ht : 0 < t)
    (hfall : g * Real.cos phi * t ^ 2 / 2 = D * Real.cos phi) :
    t = Real.sqrt (2 * D / g) := by
  have hc : 0 < Real.cos phi := Real.cos_pos_of_mem_Ioo hphi
  have h1 : g * t ^ 2 / 2 = D := by
    apply mul_right_cancel₀ hc.ne'
    rw [← hfall]; ring
  have h2 : t ^ 2 = 2 * D / g := by
    rw [eq_div_iff hg.ne']; linarith
  rw [← h2, Real.sqrt_sq ht.le]

theorem W4b_StationaryAction_maupertuis_lever_equilibrium
    (m₁ m₂ L : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    IsMinOn (fun z : ℝ => m₁ * z ^ 2 + m₂ * (L - z) ^ 2) Set.univ (m₂ * L / (m₁ + m₂)) := by
  rw [isMinOn_iff]
  intro z _
  have hs : 0 < m₁ + m₂ := by linarith
  have hz0 : m₂ * L / (m₁ + m₂) * (m₁ + m₂) = m₂ * L := by field_simp
  set z0 := m₂ * L / (m₁ + m₂) with hz0def
  show m₁ * z0 ^ 2 + m₂ * (L - z0) ^ 2 ≤ m₁ * z ^ 2 + m₂ * (L - z) ^ 2
  have key : m₁ * z ^ 2 + m₂ * (L - z) ^ 2 - (m₁ * z0 ^ 2 + m₂ * (L - z0) ^ 2)
      = (m₁ + m₂) * (z - z0) ^ 2 := by
    linear_combination (2 * (z - z0)) * hz0
  nlinarith [mul_nonneg hs.le (sq_nonneg (z - z0))]

theorem W4b_StationaryAction_heron_law_of_reflection
    (a b d x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : IsMinOn (fun s : ℝ => Real.sqrt (a ^ 2 + s ^ 2)
        + Real.sqrt (b ^ 2 + (d - s) ^ 2)) Set.univ x) :
    x / Real.sqrt (a ^ 2 + x ^ 2) = (d - x) / Real.sqrt (b ^ 2 + (d - x) ^ 2) := by
  have hA : a ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hB : b ^ 2 + (d - x) ^ 2 ≠ 0 := by positivity
  have h1 := ((W4b_StationaryAction_hsq x).const_add (a ^ 2)).sqrt hA
  have h2 := ((W4b_StationaryAction_hsq2 d x).const_add (b ^ 2)).sqrt hB
  have hz := (hmin.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero (h1.add h2)
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  rw [neg_div, mul_div_mul_left _ _ h2ne, mul_div_mul_left _ _ h2ne] at hz
  linarith

theorem W4b_StationaryAction_snell_law_of_stationary_time
    (a b d v₁ v₂ x : ℝ) (ha : 0 < a) (hb : 0 < b) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hstat : deriv (fun s : ℝ => Real.sqrt (a ^ 2 + s ^ 2) / v₁
        + Real.sqrt (b ^ 2 + (d - s) ^ 2) / v₂) x = 0) :
    x / Real.sqrt (a ^ 2 + x ^ 2) / v₁
      = (d - x) / Real.sqrt (b ^ 2 + (d - x) ^ 2) / v₂ := by
  have hA : a ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hB : b ^ 2 + (d - x) ^ 2 ≠ 0 := by positivity
  have h1 := ((W4b_StationaryAction_hsq x).const_add (a ^ 2)).sqrt hA
  have h2 := ((W4b_StationaryAction_hsq2 d x).const_add (b ^ 2)).sqrt hB
  have h := (h1.div_const v₁).add (h2.div_const v₂)
  have e : deriv (fun s : ℝ => Real.sqrt (a ^ 2 + s ^ 2) / v₁
      + Real.sqrt (b ^ 2 + (d - s) ^ 2) / v₂) x =
      2 * x / (2 * Real.sqrt (a ^ 2 + x ^ 2)) / v₁ +
        -(2 * (d - x)) / (2 * Real.sqrt (b ^ 2 + (d - x) ^ 2)) / v₂ := h.deriv
  rw [e] at hstat
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  rw [neg_div, mul_div_mul_left _ _ h2ne, mul_div_mul_left _ _ h2ne, neg_div] at hstat
  linarith

/-! ## Euler–Lagrange computations for explicit Lagrangians -/

theorem W4b_StationaryAction_harmonic_oscillator_equation_of_motion
    (m k : ℝ) (q : ℝ → ℝ) (t₁ t₂ : ℝ) (hq : ContDiff ℝ 2 q) :
    (∀ t ∈ Set.Icc t₁ t₂,
        eulerLagrangeExpr (fun u v _ => m * v ^ 2 / 2 - k * u ^ 2 / 2) q t = 0) ↔
      ∀ t ∈ Set.Icc t₁ t₂, m * deriv (deriv q) t + k * q t = 0 := by
  have hq'd : Differentiable ℝ (deriv q) := (W4b_StationaryAction_dd hq).differentiable (by simp)
  have hY : ∀ u v x : ℝ,
      partialY (fun u v _ => m * v ^ 2 / 2 - k * u ^ 2 / 2) u v x = -(k * u) := by
    intro u v x
    unfold partialY
    exact ((((W4b_StationaryAction_hsq u).const_mul k).div_const 2).const_sub
      (m * v ^ 2 / 2)).deriv.trans (by ring)
  have hV : ∀ u v x : ℝ,
      partialV (fun u v _ => m * v ^ 2 / 2 - k * u ^ 2 / 2) u v x = m * v := by
    intro u v x
    unfold partialV
    exact ((((W4b_StationaryAction_hsq v).const_mul m).div_const 2).sub_const
      (k * u ^ 2 / 2)).deriv.trans (by ring)
  have key : ∀ t, eulerLagrangeExpr (fun u v _ => m * v ^ 2 / 2 - k * u ^ 2 / 2) q t
      = -(m * deriv (deriv q) t + k * q t) := by
    intro t
    unfold eulerLagrangeExpr
    rw [hY]
    have e : (fun s => partialV (fun u v _ => m * v ^ 2 / 2 - k * u ^ 2 / 2) (q s)
        (deriv q s) s) = fun s => m * deriv q s := funext fun s => hV _ _ _
    rw [e, deriv_const_mul _ (hq'd t)]
    ring
  constructor
  · intro h t ht
    have := h t ht
    rw [key] at this
    linarith
  · intro h t ht
    rw [key]
    linarith [h t ht]

theorem W4b_StationaryAction_plane_pendulum_equation_of_motion
    (m g l : ℝ) (hm : m ≠ 0) (hl : l ≠ 0) (θ : ℝ → ℝ) (t₁ t₂ : ℝ) (hθ : ContDiff ℝ 2 θ) :
    (∀ t ∈ Set.Icc t₁ t₂,
        eulerLagrangeExpr
          (fun u v _ => m * l ^ 2 * v ^ 2 / 2 - m * g * l * (1 - Real.cos u)) θ t = 0) ↔
      ∀ t ∈ Set.Icc t₁ t₂, deriv (deriv θ) t + (g / l) * Real.sin (θ t) = 0 := by
  have hθ'd : Differentiable ℝ (deriv θ) := (W4b_StationaryAction_dd hθ).differentiable (by simp)
  have hY : ∀ u v x : ℝ,
      partialY (fun u v _ => m * l ^ 2 * v ^ 2 / 2 - m * g * l * (1 - Real.cos u)) u v x
        = -(m * g * l * Real.sin u) := by
    intro u v x
    unfold partialY
    exact ((((Real.hasDerivAt_cos u).const_sub 1).const_mul (m * g * l)).const_sub
      (m * l ^ 2 * v ^ 2 / 2)).deriv.trans (by ring)
  have hV : ∀ u v x : ℝ,
      partialV (fun u v _ => m * l ^ 2 * v ^ 2 / 2 - m * g * l * (1 - Real.cos u)) u v x
        = m * l ^ 2 * v := by
    intro u v x
    unfold partialV
    exact ((((W4b_StationaryAction_hsq v).const_mul (m * l ^ 2)).div_const 2).sub_const
      (m * g * l * (1 - Real.cos u))).deriv.trans (by ring)
  have hgl : g / l * l = g := by field_simp
  have key : ∀ t, eulerLagrangeExpr
      (fun u v _ => m * l ^ 2 * v ^ 2 / 2 - m * g * l * (1 - Real.cos u)) θ t
      = -(m * l ^ 2) * (deriv (deriv θ) t + (g / l) * Real.sin (θ t)) := by
    intro t
    unfold eulerLagrangeExpr
    rw [hY]
    have e : (fun s => partialV
        (fun u v _ => m * l ^ 2 * v ^ 2 / 2 - m * g * l * (1 - Real.cos u)) (θ s)
        (deriv θ s) s) = fun s => m * l ^ 2 * deriv θ s := funext fun s => hV _ _ _
    rw [e, deriv_const_mul _ (hθ'd t)]
    linear_combination (m * l * Real.sin (θ t)) * hgl
  have hne : -(m * l ^ 2) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hm (pow_ne_zero 2 hl))
  constructor
  · intro h t ht
    have := h t ht
    rw [key] at this
    exact (mul_eq_zero.mp this).resolve_left hne
  · intro h t ht
    rw [key, h t ht, mul_zero]

theorem W4b_StationaryAction_partialV_const_of_cyclic
    (f : ℝ → ℝ → ℝ → ℝ) (y : ℝ → ℝ) (x₁ x₂ : ℝ)
    (hf : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hy : ContDiff ℝ 2 y)
    (hcyclic : ∀ u v x : ℝ, partialY f u v x = 0)
    (hEL : ∀ x ∈ Set.Icc x₁ x₂, eulerLagrangeExpr f y x = 0) :
    ∀ x ∈ Set.Icc x₁ x₂,
      partialV f (y x) (deriv y x) x = partialV f (y x₁) (deriv y x₁) x₁ := by
  have hG := W4b_StationaryAction_pVC1 f _ (fun _ _ _ => rfl) hf y hy
  apply W4b_StationaryAction_const_on (fun t => partialV f (y t) (deriv y t) t) x₁ x₂
    (hG.differentiable (by simp))
  intro x hx
  have := hEL x hx
  unfold eulerLagrangeExpr at this
  rw [hcyclic] at this
  linarith

/-! ## First variation, fundamental lemma, Euler–Lagrange -/

theorem W4b_StationaryAction_fv_core (f : ℝ → ℝ → ℝ → ℝ) (F : ℝ × ℝ × ℝ → ℝ)
    (hFf : ∀ u v x, f u v x = F (u, v, x)) (hf : ContDiff ℝ 2 F)
    (y η : ℝ → ℝ) (x₁ x₂ : ℝ) (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 2 η) :
    deriv (fun a : ℝ => action f (vary y η a) x₁ x₂) 0 =
      ∫ x in x₁..x₂, (η x * partialY f (y x) (deriv y x) x
        + deriv η x * partialV f (y x) (deriv y x) x) := by
  have hFd : Differentiable ℝ F := hf.differentiable (by simp)
  have hDc : Continuous (fderiv ℝ F) :=
    (hf.fderiv_right (le_of_eq one_add_one_eq_two)).continuous
  have hyd : Differentiable ℝ y := hy.differentiable (by simp)
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hyc : Continuous y := hyd.continuous
  have hηc : Continuous η := hηd.continuous
  have hy'c : Continuous (deriv y) := (W4b_StationaryAction_dd hy).continuous
  have hη'c : Continuous (deriv η) := (W4b_StationaryAction_dd hη).continuous
  have hvd : ∀ a x : ℝ, deriv (vary y η a) x = deriv y x + a * deriv η x :=
    fun a x => ((hyd x).hasDerivAt.add ((hηd x).hasDerivAt.const_mul a)).deriv
  have hfun : (fun a : ℝ => action f (vary y η a) x₁ x₂) =
      fun a => ∫ x in x₁..x₂, F (y x + a * η x, deriv y x + a * deriv η x, x) := by
    funext a
    unfold action
    simp only [hvd, vary, hFf]
  have hg : ∀ x a : ℝ, HasDerivAt (fun a => (y x + a * η x, deriv y x + a * deriv η x, x))
      (η x, deriv η x, (0 : ℝ)) a := fun x a =>
    ((hasDerivAt_mul_const (η x)).const_add (y x)).prodMk
      (((hasDerivAt_mul_const (deriv η x)).const_add (deriv y x)).prodMk (hasDerivAt_const a x))
  have hdiff : ∀ x a : ℝ, HasDerivAt (fun a => F (y x + a * η x, deriv y x + a * deriv η x, x))
      (fderiv ℝ F (y x + a * η x, deriv y x + a * deriv η x, x) (η x, deriv η x, 0)) a :=
    fun x a => (hFd _).hasFDerivAt.comp_hasDerivAt a (hg x a)
  have hpc : Continuous (fun q : ℝ × ℝ =>
      (y q.2 + q.1 * η q.2, deriv y q.2 + q.1 * deriv η q.2, q.2)) := by fun_prop
  have hcont2 : Continuous (fun q : ℝ × ℝ =>
      fderiv ℝ F (y q.2 + q.1 * η q.2, deriv y q.2 + q.1 * deriv η q.2, q.2)
        (η q.2, deriv η q.2, (0 : ℝ))) :=
    (hDc.comp hpc).clm_apply (by fun_prop)
  have hcont1 : ∀ a : ℝ, Continuous (fun x => F (y x + a * η x, deriv y x + a * deriv η x, x)) :=
    fun a => hFd.continuous.comp (by fun_prop)
  have hcont0 : Continuous (fun x =>
      fderiv ℝ F (y x + 0 * η x, deriv y x + 0 * deriv η x, x) (η x, deriv η x, (0 : ℝ))) :=
    hcont2.comp (continuous_const.prodMk continuous_id)
  obtain ⟨K, hK⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
    (isCompact_uIcc (a := x₁) (b := x₂))).exists_bound_of_continuousOn hcont2.continuousOn
  have hbound : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIoc x₁ x₂ → ∀ a ∈ Metric.ball (0 : ℝ) 1,
        ‖fderiv ℝ F (y x + a * η x, deriv y x + a * deriv η x, x) (η x, deriv η x, (0 : ℝ))‖
          ≤ K := by
    refine Filter.Eventually.of_forall fun x hx a ha => ?_
    have ha' : |a| < 1 := by simpa using ha
    exact hK (a, x) ⟨⟨(abs_lt.mp ha').1.le, (abs_lt.mp ha').2.le⟩, Set.uIoc_subset_uIcc hx⟩
  obtain ⟨-, hder⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun a x => F (y x + a * η x, deriv y x + a * deriv η x, x))
      (F' := fun a x => fderiv ℝ F (y x + a * η x, deriv y x + a * deriv η x, x)
        (η x, deriv η x, (0 : ℝ)))
      (x₀ := 0) (s := Metric.ball 0 1) (bound := fun _ => K) (a := x₁) (b := x₂)
      (Metric.ball_mem_nhds 0 one_pos)
      (Filter.Eventually.of_forall fun a => (hcont1 a).aestronglyMeasurable)
      ((hcont1 0).intervalIntegrable _ _)
      hcont0.aestronglyMeasurable
      hbound
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun x _ a _ => hdiff x a)
  rw [hfun, hder.deriv]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [zero_mul, add_zero]
  rw [W4b_StationaryAction_pY f F hFf hFd, W4b_StationaryAction_pV f F hFf hFd]
  have e : ((η x, deriv η x, (0 : ℝ)) : ℝ × ℝ × ℝ) =
      η x • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + deriv η x • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) := by
    simp
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem W4b_StationaryAction_first_variation_of_action
    (f : ℝ → ℝ → ℝ → ℝ) (y η : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂)
    (hf : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hy : ContDiff ℝ 2 y) (hη : ContDiff ℝ 2 η) :
    deriv (fun a : ℝ => action f (vary y η a) x₁ x₂) 0 =
      ∫ x in x₁..x₂, (η x * partialY f (y x) (deriv y x) x
        + deriv η x * partialV f (y x) (deriv y x) x) :=
  W4b_StationaryAction_fv_core f _ (fun _ _ _ => rfl) hf y η x₁ x₂ hy hη

theorem solution
    (g : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ < x₂)
    (hg : ContinuousOn g (Set.Icc x₁ x₂))
    (h : ∀ η : ℝ → ℝ, IsAdmissibleVariation η x₁ x₂ → (∫ x in x₁..x₂, η x * g x) = 0) :
    ∀ x ∈ Set.Icc x₁ x₂, g x = 0 := by
  have hint : ∀ c ∈ Set.Ioo x₁ x₂, g c = 0 := by
    intro c hc
    by_contra hne
    have hgc : ContinuousAt g c := hg.continuousAt (Icc_mem_nhds hc.1 hc.2)
    have hpos : 0 < g c * g c := mul_self_pos.mpr hne
    have hev : ∀ᶠ z in nhds c, 0 < g c * g z ∧ z ∈ Set.Ioo x₁ x₂ :=
      (Filter.Tendsto.eventually (continuousAt_const.mul hgc) (lt_mem_nhds hpos)).and
        (Ioo_mem_nhds hc.1 hc.2)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    let φ : ContDiffBump c := ⟨δ / 2, δ, by positivity, by linarith⟩
    have hφpos : ∀ z, dist z c < δ → 0 < φ z := by
      intro z hz
      have hmem : z ∈ Function.support φ := by
        rw [φ.support_eq]; exact hz
      exact lt_of_le_of_ne φ.nonneg (Ne.symm (Function.mem_support.mp hmem))
    have hφ0 : ∀ z, δ ≤ dist z c → φ z = 0 := fun z hz => φ.zero_of_le_dist hz
    have hx1 : δ ≤ dist x₁ c := by
      by_contra hlt
      push_neg at hlt
      exact lt_irrefl _ (hball hlt).2.1
    have hx2 : δ ≤ dist x₂ c := by
      by_contra hlt
      push_neg at hlt
      exact lt_irrefl _ (hball hlt).2.2
    have hadm : IsAdmissibleVariation φ x₁ x₂ := ⟨φ.contDiff, hφ0 _ hx1, hφ0 _ hx2⟩
    have h0 := h φ hadm
    have h1 : ∫ x in x₁..x₂, φ x * (g c * g x) = 0 := by
      have e : (fun x => φ x * (g c * g x)) = fun x => g c * (φ x * g x) := by
        funext x; ring
      rw [e, intervalIntegral.integral_const_mul, h0, mul_zero]
    have hnn : ∀ z, 0 ≤ φ z * (g c * g z) := by
      intro z
      by_cases hz : dist z c < δ
      · exact (mul_pos (hφpos z hz) (hball hz).1).le
      · rw [hφ0 z (not_lt.mp hz), zero_mul]
    have hII : IntervalIntegrable (fun x => φ x * (g c * g x)) MeasureTheory.volume x₁ x₂ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx.le]
      exact (show ContDiff ℝ 1 (φ : ℝ → ℝ) from φ.contDiff).continuous.continuousOn.mul
        (continuousOn_const.mul hg)
    have hpos_int : 0 < ∫ x in x₁..x₂, φ x * (g c * g x) := by
      rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall hnn) hII]
      refine ⟨hx, ?_⟩
      have hsub : Metric.ball c δ ⊆
          Function.support (fun z => φ z * (g c * g z)) ∩ Set.Ioc x₁ x₂ := by
        intro z hz
        exact ⟨(mul_pos (hφpos z hz) (hball hz).1).ne', Set.Ioo_subset_Ioc_self (hball hz).2⟩
      exact (Metric.measure_ball_pos MeasureTheory.volume c hδ).trans_le
        (MeasureTheory.measure_mono hsub)
    linarith
  have heq : Set.EqOn g 0 (Set.Icc x₁ x₂) :=
    Set.EqOn.of_subset_closure (fun c hc => hint c hc) hg continuousOn_const
      Set.Ioo_subset_Icc_self (closure_Ioo hx.ne).ge
  intro x hx'
  exact heq hx'

theorem W4b_StationaryAction_euler_lagrange_of_stationary_action
    (f : ℝ → ℝ → ℝ → ℝ) (y : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ < x₂)
    (hf : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hy : ContDiff ℝ 2 y)
    (hstat : IsStationaryPath f y x₁ x₂) :
    ∀ x ∈ Set.Icc x₁ x₂, eulerLagrangeExpr f y x = 0 := by
  have hA : Continuous (fun t => partialY f (y t) (deriv y t) t) :=
    (W4b_StationaryAction_pYC1 f _ (fun _ _ _ => rfl) hf y hy).continuous
  have hG : ContDiff ℝ 1 (fun t => partialV f (y t) (deriv y t) t) :=
    W4b_StationaryAction_pVC1 f _ (fun _ _ _ => rfl) hf y hy
  have hGd : Differentiable ℝ (fun t => partialV f (y t) (deriv y t) t) :=
    hG.differentiable (by simp)
  have hG'c : Continuous (deriv (fun t => partialV f (y t) (deriv y t) t)) :=
    (contDiff_one_iff_deriv.mp hG).2
  refine solution
    (eulerLagrangeExpr f y) x₁ x₂ hx (hA.sub hG'c).continuousOn ?_
  intro η hη
  obtain ⟨hηC, hη1, hη2⟩ := hη
  have hfv := W4b_StationaryAction_first_variation_of_action f y η x₁ x₂ hx.le hf hy hηC
  rw [hstat η ⟨hηC, hη1, hη2⟩] at hfv
  have hηd : Differentiable ℝ η := hηC.differentiable (by simp)
  have hηc : Continuous η := hηd.continuous
  have hη'c : Continuous (deriv η) := (W4b_StationaryAction_dd hηC).continuous
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => partialV f (y t) (deriv y t) t)
    (u' := deriv (fun t => partialV f (y t) (deriv y t) t)) (v := η) (v' := deriv η)
    (a := x₁) (b := x₂)
    (fun x _ => (hGd x).hasDerivAt) (fun x _ => (hηd x).hasDerivAt)
    (hG'c.intervalIntegrable _ _) (hη'c.intervalIntegrable _ _)
  rw [hη1, hη2, mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  have i1 : IntervalIntegrable (fun x => η x * partialY f (y x) (deriv y x) x)
      MeasureTheory.volume x₁ x₂ := (hηc.mul hA).intervalIntegrable _ _
  have i2 : IntervalIntegrable
      (fun x => deriv (fun t => partialV f (y t) (deriv y t) t) x * η x)
      MeasureTheory.volume x₁ x₂ := (hG'c.mul hηc).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x => deriv η x * partialV f (y x) (deriv y x) x)
      MeasureTheory.volume x₁ x₂ := (hη'c.mul hG.continuous).intervalIntegrable _ _
  have split1 : ∫ x in x₁..x₂, η x * eulerLagrangeExpr f y x =
      (∫ x in x₁..x₂, η x * partialY f (y x) (deriv y x) x) -
        ∫ x in x₁..x₂, deriv (fun t => partialV f (y t) (deriv y t) t) x * η x := by
    rw [← intervalIntegral.integral_sub i1 i2]
    congr 1
    funext x
    unfold eulerLagrangeExpr
    ring
  have split2 := intervalIntegral.integral_add i1 i3
  have e3 : ∫ x in x₁..x₂, deriv η x * partialV f (y x) (deriv y x) x =
      ∫ x in x₁..x₂, partialV f (y x) (deriv y x) x * deriv η x := by
    congr 1
    funext x
    ring
  rw [split1]
  linarith

theorem W4b_StationaryAction_inj {v w : ℝ}
    (h : v / Real.sqrt (1 + v ^ 2) = w / Real.sqrt (1 + w ^ 2)) : v = w := by
  have hA : 0 < Real.sqrt (1 + v ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < Real.sqrt (1 + w ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hA2 : Real.sqrt (1 + v ^ 2) ^ 2 = 1 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hB2 : Real.sqrt (1 + w ^ 2) ^ 2 = 1 + w ^ 2 := Real.sq_sqrt (by positivity)
  rw [div_eq_div_iff hA.ne' hB.ne'] at h
  have h2 : (v * Real.sqrt (1 + w ^ 2)) ^ 2 = (w * Real.sqrt (1 + v ^ 2)) ^ 2 := by rw [h]
  rw [mul_pow, mul_pow, hA2, hB2] at h2
  have hsq' : v ^ 2 = w ^ 2 := by linear_combination h2
  have hvw : 0 ≤ v * w := by
    have e : v * w * (Real.sqrt (1 + v ^ 2) * Real.sqrt (1 + w ^ 2)) =
        (w * Real.sqrt (1 + v ^ 2)) * (w * Real.sqrt (1 + v ^ 2)) := by
      calc v * w * (Real.sqrt (1 + v ^ 2) * Real.sqrt (1 + w ^ 2))
          = (v * Real.sqrt (1 + w ^ 2)) * (w * Real.sqrt (1 + v ^ 2)) := by ring
        _ = (w * Real.sqrt (1 + v ^ 2)) * (w * Real.sqrt (1 + v ^ 2)) := by rw [h]
    have : 0 ≤ v * w * (Real.sqrt (1 + v ^ 2) * Real.sqrt (1 + w ^ 2)) := by
      rw [e]; exact mul_self_nonneg _
    exact (mul_nonneg_iff_of_pos_right (mul_pos hA hB)).mp this
  have hprod : (v - w) * (v + w) = 0 := by linear_combination hsq'
  rcases mul_eq_zero.mp hprod with h1 | h1
  · linarith
  · have hw : w = -v := by linarith
    rw [hw] at hvw ⊢
    nlinarith [sq_nonneg v]

theorem W4b_StationaryAction_stationary_arclength_is_affine
    (y : ℝ → ℝ) (x₁ x₂ : ℝ) (hx : x₁ < x₂) (hy : ContDiff ℝ 2 y)
    (hstat : IsStationaryPath (fun _ v _ => Real.sqrt (1 + v ^ 2)) y x₁ x₂) :
    ∃ c b : ℝ, ∀ x ∈ Set.Icc x₁ x₂, y x = c * x + b := by
  have hf : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ =>
      (fun (_ : ℝ) (v : ℝ) (_ : ℝ) => Real.sqrt (1 + v ^ 2)) p.1 p.2.1 p.2.2) := by
    show ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => Real.sqrt (1 + p.2.1 ^ 2))
    exact (by fun_prop : ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => 1 + p.2.1 ^ 2)).sqrt
      (fun p => by positivity)
  have hEL := W4b_StationaryAction_euler_lagrange_of_stationary_action
    (fun _ v _ => Real.sqrt (1 + v ^ 2)) y x₁ x₂ hx hf hy hstat
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hV : ∀ u v x : ℝ, partialV (fun _ v _ => Real.sqrt (1 + v ^ 2)) u v x
      = v / Real.sqrt (1 + v ^ 2) := by
    intro u v x
    unfold partialV
    have h := ((W4b_StationaryAction_hsq v).const_add 1).sqrt
      (by positivity : (1 : ℝ) + v ^ 2 ≠ 0)
    exact h.deriv.trans (mul_div_mul_left _ _ h2ne)
  have hY : ∀ u v x : ℝ, partialY (fun _ v _ => Real.sqrt (1 + v ^ 2)) u v x = 0 := by
    intro u v x
    unfold partialY
    exact deriv_const _ _
  have hG1 := W4b_StationaryAction_pVC1 (fun _ v _ => Real.sqrt (1 + v ^ 2)) _
    (fun _ _ _ => rfl) hf y hy
  have hconst := W4b_StationaryAction_const_on
    (fun t => partialV (fun _ v _ => Real.sqrt (1 + v ^ 2)) (y t) (deriv y t) t) x₁ x₂
    (hG1.differentiable (by simp)) (by
      intro x hx'
      have := hEL x hx'
      unfold eulerLagrangeExpr at this
      rw [hY] at this
      linarith)
  have hy'c : ∀ x ∈ Set.Icc x₁ x₂, deriv y x = deriv y x₁ := by
    intro x hx'
    have h : partialV (fun _ v _ => Real.sqrt (1 + v ^ 2)) (y x) (deriv y x) x =
        partialV (fun _ v _ => Real.sqrt (1 + v ^ 2)) (y x₁) (deriv y x₁) x₁ := hconst x hx'
    rw [hV, hV] at h
    exact W4b_StationaryAction_inj h
  have hyd : Differentiable ℝ y := hy.differentiable (by simp)
  refine ⟨deriv y x₁, y x₁ - deriv y x₁ * x₁, ?_⟩
  have hK := W4b_StationaryAction_const_on (fun x => y x - deriv y x₁ * x) x₁ x₂
    (hyd.sub (differentiable_id.const_mul (deriv y x₁))) (by
      intro x hx'
      have hd : HasDerivAt (fun x => y x - deriv y x₁ * x) (deriv y x - deriv y x₁ * 1) x :=
        (hyd x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul (deriv y x₁))
      rw [hd.deriv, hy'c x hx']
      ring)
  intro x hx'
  have h2 : y x - deriv y x₁ * x = y x₁ - deriv y x₁ * x₁ := hK x hx'
  linarith
