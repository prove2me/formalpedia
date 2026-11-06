-- Prove2me | solution 1 for OTDRO.StrongCvx.F_strongly_concave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:33:42.14204+00:00
-- url     : https://prove2.me/submissions/f6ef7604-464c-4a17-8f53-645624fd6844

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Kernel

open MeasureTheory Matrix

namespace OTDROL8

variable {d : ℕ}

lemma mulVec_inv_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosDef) (b : Fin d → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).1 hM.isUnit), one_mulVec]

lemma quadInv_eq (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) :
    OTDRO.Dual.quadInv A β x =
      dotProduct ((A x)⁻¹ *ᵥ β.ofLp) (A x *ᵥ ((A x)⁻¹ *ᵥ β.ofLp)) := by
  unfold OTDRO.Dual.quadInv
  rw [mulVec_inv_mulVec _ (hA x), dotProduct_comm]

lemma quadInv_nonneg (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ OTDRO.Dual.quadInv A β x := by
  rw [quadInv_eq A hA]
  have := (hA x).posSemidef.dotProduct_mulVec_nonneg ((A x)⁻¹ *ᵥ β.ofLp)
  simpa using this

lemma quadInv_le (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β x : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ v : EuclideanSpace ℝ (Fin d), ρ * ‖v‖ ^ 2 ≤ dotProduct v.ofLp (A x *ᵥ v.ofLp)) :
    OTDRO.Dual.quadInv A β x ≤ ‖β‖ ^ 2 / ρ := by
  set W : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp) with hW
  have h1 : ρ * ‖W‖ ^ 2 ≤ OTDRO.Dual.quadInv A β x := by
    rw [quadInv_eq A hA]; exact hx W
  have h2 : OTDRO.Dual.quadInv A β x ≤ ‖β‖ * ‖W‖ := by
    have : OTDRO.Dual.quadInv A β x = inner ℝ W β := by
      unfold OTDRO.Dual.quadInv
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [hW]
    rw [this, mul_comm]
    exact real_inner_le_norm W β
  have hq0 := quadInv_nonneg A hA β x
  rw [le_div_iff₀ hρ]
  have hW0 : 0 ≤ ‖W‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖β‖ := norm_nonneg _
  -- ρ‖W‖ ≤ ‖β‖
  have h3 : ρ * ‖W‖ ≤ ‖β‖ := by
    rcases eq_or_lt_of_le hW0 with h | h
    · rw [← h]; simp [hb0]
    · nlinarith
  nlinarith

lemma quadInv_pos (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) : 0 < OTDRO.Dual.quadInv A β x := by
  unfold OTDRO.Dual.quadInv
  have h := (hA x).inv.dotProduct_mulVec_pos (x := β.ofLp) (by
    intro h0; apply hβ; ext i; simpa using congrFun h0 i)
  simpa using h

lemma quadInv_lip (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).PosDef) (x : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) (hρ : 0 < ρ)
    (hx : ∀ v : EuclideanSpace ℝ (Fin d), ρ * ‖v‖ ^ 2 ≤ dotProduct v.ofLp (A x *ᵥ v.ofLp))
    (β β' : EuclideanSpace ℝ (Fin d)) :
    |OTDRO.Dual.quadInv A β x - OTDRO.Dual.quadInv A β' x| ≤ ‖β - β'‖ * ‖β + β'‖ / ρ := by
  set W := (A x)⁻¹
  have hWs : Wᵀ = W := by
    have hMs : (A x)ᵀ = A x := by
      have := (hA x).isHermitian
      ext i j
      have h := congrFun (congrFun this i) j
      simpa using h
    simp only [W]; rw [transpose_nonsing_inv, hMs]
  -- ‖W v‖ ≤ ‖v‖ / ρ
  have hWv : ∀ v : EuclideanSpace ℝ (Fin d),
      ‖(WithLp.toLp 2 (W *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin d))‖ ≤ ‖v‖ / ρ := by
    intro v
    set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (W *ᵥ v.ofLp)
    have h1 : ρ * ‖w‖ ^ 2 ≤ inner ℝ w v := by
      have := hx w
      have e : dotProduct w.ofLp (A x *ᵥ w.ofLp) = inner ℝ w v := by
        simp only [w, W]
        rw [mulVec_inv_mulVec _ (hA x), EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct_comm]
      linarith
    have h2 : inner ℝ w v ≤ ‖w‖ * ‖v‖ := real_inner_le_norm w v
    rw [le_div_iff₀ hρ]
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    rcases eq_or_lt_of_le hw0 with h | h
    · rw [← h]; simp
    · nlinarith
  have key : OTDRO.Dual.quadInv A β x - OTDRO.Dual.quadInv A β' x =
      inner ℝ (β - β') (WithLp.toLp 2 (W *ᵥ (β + β').ofLp) : EuclideanSpace ℝ (Fin d)) := by
    unfold OTDRO.Dual.quadInv
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [WithLp.ofLp_add, WithLp.ofLp_sub, mulVec_add, star_trivial]
    have hsym : dotProduct β'.ofLp (W *ᵥ β.ofLp) = dotProduct β.ofLp (W *ᵥ β'.ofLp) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hWs, dotProduct_comm]
    simp only [W] at hsym ⊢
    simp only [dotProduct_add, dotProduct_sub, sub_dotProduct, add_dotProduct]
    rw [dotProduct_comm ((A x)⁻¹ *ᵥ β.ofLp) β.ofLp, dotProduct_comm ((A x)⁻¹ *ᵥ β'.ofLp) β.ofLp,
      dotProduct_comm ((A x)⁻¹ *ᵥ β.ofLp) β'.ofLp, dotProduct_comm ((A x)⁻¹ *ᵥ β'.ofLp) β'.ofLp]
    rw [hsym]; ring
  rw [key]
  calc |inner ℝ (β - β') (WithLp.toLp 2 (W *ᵥ (β + β').ofLp) : EuclideanSpace ℝ (Fin d))|
      ≤ ‖β - β'‖ * ‖(WithLp.toLp 2 (W *ᵥ (β + β').ofLp) : EuclideanSpace ℝ (Fin d))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖β - β'‖ * (‖β + β'‖ / ρ) := mul_le_mul_of_nonneg_left (hWv _) (norm_nonneg _)
    _ = ‖β - β'‖ * ‖β + β'‖ / ρ := by ring

lemma ae_quadInv_le_essSup_all (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ρmin ρmax : ℝ)
    (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) :
    ∀ᵐ x ∂P0, ∀ β : EuclideanSpace ℝ (Fin d),
      OTDRO.Dual.quadInv A β x ≤ essSup (fun y => OTDRO.Dual.quadInv A β y) P0 := by
  have hρ := hA.rhoMin_pos
  have hbu : ∀ β : EuclideanSpace ℝ (Fin d),
      Filter.IsBoundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) := by
    intro β
    apply Filter.isBoundedUnder_of_eventually_le (a := ‖β‖ ^ 2 / ρmin)
    filter_upwards [hA.eig_bounds] with x hx
    exact quadInv_le A hA.posDef β x ρmin hρ (fun v => (hx v).1)
  have hcob : ∀ β : EuclideanSpace ℝ (Fin d),
      Filter.IsCoboundedUnder (· ≤ ·) (ae P0) (fun x => OTDRO.Dual.quadInv A β x) :=
    fun β => Filter.isCoboundedUnder_le_of_le (ae P0) (fun x => quadInv_nonneg A hA.posDef β x)
  -- Q is "Lipschitz"
  have hQlip : ∀ β β' : EuclideanSpace ℝ (Fin d),
      essSup (fun y => OTDRO.Dual.quadInv A β' y) P0 ≤
        essSup (fun y => OTDRO.Dual.quadInv A β y) P0 + ‖β - β'‖ * ‖β + β'‖ / ρmin := by
    intro β β'
    apply essSup_le_of_ae_le _ _ (hcob β')
    filter_upwards [ae_le_essSup (hbu β), hA.eig_bounds] with y hy1 hy2
    have := quadInv_lip A hA.posDef y ρmin hρ (fun v => (hy2 v).1) β β'
    have h' := neg_abs_le (OTDRO.Dual.quadInv A β y - OTDRO.Dual.quadInv A β' y)
    show OTDRO.Dual.quadInv A β' y ≤ _
    linarith
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin d))
  have h1 : ∀ᵐ x ∂P0, ∀ β ∈ D, OTDRO.Dual.quadInv A β x ≤
      essSup (fun y => OTDRO.Dual.quadInv A β y) P0 :=
    (ae_ball_iff hDc).2 (fun β _ => ae_le_essSup (hbu β))
  filter_upwards [h1, hA.eig_bounds] with x hx hx2
  intro β
  apply le_of_forall_pos_le_add
  intro ε hε
  set η := min 1 (ε * ρmin / (2 * (2 * ‖β‖ + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨β', hβ', hβ'D⟩ := Metric.dense_iff.1 hDd β η hη
  rw [Metric.mem_ball, dist_eq_norm] at hβ'
  have hβ'' : ‖β - β'‖ < η := by rw [norm_sub_rev]; exact hβ'
  have hsum : ‖β + β'‖ ≤ 2 * ‖β‖ + 1 := by
    have : ‖β'‖ ≤ ‖β‖ + η := by
      have := norm_le_norm_add_norm_sub' β' β
      rw [norm_sub_rev] at this; linarith
    have := norm_add_le β β'
    have : η ≤ 1 := min_le_left _ _
    linarith
  set c := ‖β - β'‖ * ‖β + β'‖ / ρmin
  have hc : 2 * c ≤ ε := by
    simp only [c]
    have h3 : ‖β - β'‖ * ‖β + β'‖ ≤ η * (2 * ‖β‖ + 1) :=
      mul_le_mul hβ''.le hsum (norm_nonneg _) hη.le
    have h4 : η ≤ ε * ρmin / (2 * (2 * ‖β‖ + 1)) := min_le_right _ _
    have h5 : η * (2 * ‖β‖ + 1) ≤ ε * ρmin / 2 := by
      have hp : 0 < 2 * ‖β‖ + 1 := by positivity
      calc η * (2 * ‖β‖ + 1) ≤ ε * ρmin / (2 * (2 * ‖β‖ + 1)) * (2 * ‖β‖ + 1) :=
            mul_le_mul_of_nonneg_right h4 hp.le
        _ = ε * ρmin / 2 := by field_simp
    rw [mul_div_assoc', div_le_iff₀ hρ]
    linarith
  have hl1 := quadInv_lip A hA.posDef x ρmin hρ (fun v => (hx2 v).1) β β'
  have hl2 := hQlip β β'
  have hl3 : essSup (fun y => OTDRO.Dual.quadInv A β' y) P0 ≤
      essSup (fun y => OTDRO.Dual.quadInv A β y) P0 + c := hl2
  have hx' := hx β' hβ'D
  have := le_abs_self (OTDRO.Dual.quadInv A β x - OTDRO.Dual.quadInv A β' x)
  linarith

/-- Scalar strong concavity of `γ ↦ ℓ(s + γ c q) − λ c (γ² q − 1)`. -/
lemma scalar_strong (ℓ : ℝ → ℝ) (hd : Differentiable ℝ ℓ) (hdd : Differentiable ℝ (deriv ℓ))
    (M : ℝ) (hM : ∀ u, deriv (deriv ℓ) u ≤ M) (s c q lam : ℝ) (hc : 0 < c) (hq : 0 < q)
    (hlam : c * q * M < 2 * lam) :
    let F : ℝ → ℝ := fun γ => ℓ (s + γ * c * q) - lam * c * (γ ^ 2 * q - 1)
    let m : ℝ := c * q * (2 * lam - c * q * M)
    0 < m ∧
    (∀ γ₁ γ₂ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * F γ₁ + (1 - t) * F γ₂ + m / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 ≤
        F (t * γ₁ + (1 - t) * γ₂)) ∧
    ∃ γ : ℝ, {g : ℝ | ∀ c' : ℝ, F c' ≤ F g} = {γ} := by
  intro F m
  have hm : 0 < m := by
    have : 0 < 2 * lam - c * q * M := by linarith
    positivity
  set F' : ℝ → ℝ := fun γ => deriv ℓ (s + γ * c * q) * (c * q) - lam * c * (2 * γ * q) with hF'
  have hin : ∀ γ, HasDerivAt (fun γ : ℝ => s + γ * c * q) (c * q) γ := by
    intro γ
    have := (((hasDerivAt_id' γ).mul_const c).mul_const q).const_add s
    exact this.congr_deriv (by ring)
  have hFd : ∀ γ, HasDerivAt F (F' γ) γ := by
    intro γ
    have h1 : HasDerivAt (fun γ => ℓ (s + γ * c * q)) (deriv ℓ (s + γ * c * q) * (c * q)) γ :=
      (hd (s + γ * c * q)).hasDerivAt.comp γ (hin γ)
    have h2 : HasDerivAt (fun γ : ℝ => lam * c * (γ ^ 2 * q - 1)) (lam * c * (2 * γ * q)) γ := by
      have := (((hasDerivAt_pow 2 γ).mul_const q).sub_const 1).const_mul (lam * c)
      exact this.congr_deriv (by push_cast; ring)
    exact h1.sub h2
  have hF'd : ∀ γ, HasDerivAt F'
      (deriv (deriv ℓ) (s + γ * c * q) * (c * q) * (c * q) - lam * c * (2 * q)) γ := by
    intro γ
    have h1 : HasDerivAt (fun γ => deriv ℓ (s + γ * c * q))
        (deriv (deriv ℓ) (s + γ * c * q) * (c * q)) γ := by
      have := HasDerivAt.comp (h₂ := deriv ℓ) γ (hdd (s + γ * c * q)).hasDerivAt (hin γ)
      exact this
    have h2 : HasDerivAt (fun γ : ℝ => lam * c * (2 * γ * q)) (lam * c * (2 * q)) γ := by
      have := (((hasDerivAt_id' γ).const_mul 2).mul_const q).const_mul (lam * c)
      exact this.congr_deriv (by ring)
    exact (h1.mul_const (c * q)).sub h2
  have hF''le : ∀ γ, deriv (deriv ℓ) (s + γ * c * q) * (c * q) * (c * q) - lam * c * (2 * q)
      ≤ -m := by
    intro γ
    have h := hM (s + γ * c * q)
    have hcq : 0 ≤ (c * q) * (c * q) := by positivity
    have := mul_le_mul_of_nonneg_right h hcq
    simp only [m]; nlinarith
  -- concavity of G = F + m/2 γ²
  let G : ℝ → ℝ := fun γ => F γ + m / 2 * γ ^ 2
  have hsq : ∀ γ : ℝ, HasDerivAt (fun γ : ℝ => m / 2 * γ ^ 2) (m * γ) γ := by
    intro γ
    have := (hasDerivAt_pow 2 γ).const_mul (m / 2)
    exact this.congr_deriv (by push_cast; ring)
  have hGd : ∀ γ, HasDerivAt G (F' γ + m * γ) γ := fun γ => (hFd γ).add (hsq γ)
  have hderG : deriv G = fun γ => F' γ + m * γ := funext fun γ => (hGd γ).deriv
  have hG'd : ∀ γ, HasDerivAt (fun γ => F' γ + m * γ)
      (deriv (deriv ℓ) (s + γ * c * q) * (c * q) * (c * q) - lam * c * (2 * q) + m) γ := by
    intro γ
    have := (hF'd γ).add ((hasDerivAt_id' γ).const_mul m)
    exact this.congr_deriv (by ring)
  have hGconc : ConcaveOn ℝ Set.univ G := by
    apply concaveOn_univ_of_deriv2_nonpos (fun γ => (hGd γ).differentiableAt)
    · rw [hderG]; exact fun γ => (hG'd γ).differentiableAt
    · intro γ
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      rw [hderG, (hG'd γ).deriv]
      have := hF''le γ; linarith
  have hinterp : ∀ γ₁ γ₂ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * F γ₁ + (1 - t) * F γ₂ + m / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 ≤
        F (t * γ₁ + (1 - t) * γ₂) := by
    intro γ₁ γ₂ t ht0 ht1
    have := hGconc.2 (Set.mem_univ γ₁) (Set.mem_univ γ₂) ht0 (by linarith : 0 ≤ 1 - t)
      (by ring)
    simp only [smul_eq_mul, G] at this
    have key : m / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 =
        m / 2 * (t * γ₁ ^ 2 + (1 - t) * γ₂ ^ 2) - m / 2 * (t * γ₁ + (1 - t) * γ₂) ^ 2 := by
      ring
    rw [key]; nlinarith
  refine ⟨hm, hinterp, ?_⟩
  -- F' + m γ is antitone
  have hHanti : Antitone (fun γ => F' γ + m * γ) := by
    apply antitone_of_deriv_nonpos (fun γ => (hG'd γ).differentiableAt)
    intro γ; rw [(hG'd γ).deriv]; have := hF''le γ; linarith
  have hF'anti : Antitone F' := by
    intro a b hab
    have := hHanti hab
    simp only at this
    have : m * a ≤ m * b := mul_le_mul_of_nonneg_left hab hm.le
    linarith
  have hF'cont : Continuous F' := continuous_iff_continuousAt.2 fun γ => (hF'd γ).continuousAt
  -- zero of F'
  set a := min (F' 0 / m) 0
  set b := max (F' 0 / m) 0
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  have hFb : F' b ≤ 0 := by
    have h1 := hHanti (le_max_right (F' 0 / m) 0 : (0:ℝ) ≤ b)
    simp only [mul_zero, add_zero] at h1
    have h2 : F' 0 ≤ m * b := by
      have := le_max_left (F' 0 / m) 0
      rw [div_le_iff₀ hm] at this; linarith
    linarith
  have hFa : 0 ≤ F' a := by
    have h1 := hHanti (min_le_right (F' 0 / m) 0 : a ≤ 0)
    simp only [mul_zero, add_zero] at h1
    have h2 : m * a ≤ F' 0 := by
      have := min_le_left (F' 0 / m) 0
      rw [le_div_iff₀ hm] at this; linarith
    linarith
  obtain ⟨γs, -, hγs⟩ := intermediate_value_Icc' hab hF'cont.continuousOn ⟨hFb, hFa⟩
  have hFcont : Continuous F := continuous_iff_continuousAt.2 fun γ => (hFd γ).continuousAt
  have hmax : ∀ c', F c' ≤ F γs := by
    intro c'
    rcases le_total c' γs with h | h
    · have hmono : MonotoneOn F (Set.Iic γs) := by
        apply monotoneOn_of_deriv_nonneg (convex_Iic γs) hFcont.continuousOn
          (fun γ _ => (hFd γ).differentiableAt.differentiableWithinAt)
        intro γ hγ
        rw [interior_Iic] at hγ
        rw [(hFd γ).deriv]; rw [← hγs]; exact hF'anti (le_of_lt hγ)
      exact hmono h (Set.mem_Iic.2 le_rfl) h
    · have hanti : AntitoneOn F (Set.Ici γs) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici γs) hFcont.continuousOn
          (fun γ _ => (hFd γ).differentiableAt.differentiableWithinAt)
        intro γ hγ
        rw [interior_Ici] at hγ
        rw [(hFd γ).deriv]; rw [← hγs]; exact hF'anti (le_of_lt hγ)
      exact hanti (Set.mem_Ici.2 le_rfl) h h
  refine ⟨γs, ?_⟩
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hg
    by_contra hne
    have h := hinterp g γs (1/2) (by norm_num) (by norm_num)
    have h1 := hmax (1/2 * g + (1 - 1/2) * γs)
    have h2 := hg γs
    have h3 : 0 < (g - γs) ^ 2 := by
      have : g - γs ≠ 0 := sub_ne_zero.2 hne
      positivity
    have h4 : 0 < m / 2 * (1/2) * (1 - 1/2) * (g - γs) ^ 2 := by positivity
    linarith
  · rintro rfl; exact hmax

end OTDROL8

open OTDROL8 in
theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M) :
    ∀ᵐ x ∂P0, ∀ β ∈ B, β ≠ 0 → ∀ lam : ℝ, OTDRO.Dual.lamThr' P0 A M δ β < lam →
      ∃ m : ℝ, 0 < m ∧
        (∀ γ₁ γ₂ t : ℝ, 0 ≤ t → t ≤ 1 →
          t * OTDRO.Dual.Fobj ℓ A δ γ₁ β lam x + (1 - t) * OTDRO.Dual.Fobj ℓ A δ γ₂ β lam x +
              m / 2 * t * (1 - t) * (γ₁ - γ₂) ^ 2 ≤
            OTDRO.Dual.Fobj ℓ A δ (t * γ₁ + (1 - t) * γ₂) β lam x) ∧
        (∃ γ : ℝ, OTDRO.Dual.maximizers ℓ A δ β lam x = {γ}) ∧
        (β, lam) ∈ OTDRO.StrongCvx.UAt B ℓ A δ x := by
  filter_upwards [ae_quadInv_le_essSup_all P0 A ρmin ρmax hA] with x hx
  intro β hβB hβ0 lam hlam
  have hq : 0 < OTDRO.Dual.quadInv A β x := quadInv_pos A hA.posDef β hβ0 x
  have hc : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hM := h3.M_pos
  have hqE := hx β
  have hlam' : Real.sqrt δ * OTDRO.Dual.quadInv A β x * M < 2 * lam := by
    unfold OTDRO.Dual.lamThr' at hlam
    have : Real.sqrt δ * OTDRO.Dual.quadInv A β x * M ≤
        Real.sqrt δ * essSup (fun y => OTDRO.Dual.quadInv A β y) P0 * M := by
      apply mul_le_mul_of_nonneg_right _ hM.le
      exact mul_le_mul_of_nonneg_left hqE hc.le
    linarith
  obtain ⟨hm, hint, γ, hγ⟩ := scalar_strong ℓ h3.differentiable h3.deriv_differentiable M
    h3.second_deriv_le (inner ℝ β x) (Real.sqrt δ) (OTDRO.Dual.quadInv A β x) lam hc hq hlam'
  have hmax : OTDRO.Dual.maximizers ℓ A δ β lam x = {γ} := hγ
  refine ⟨_, hm, hint, ⟨γ, hmax⟩, hβB, ?_, γ, by rw [hmax]; rfl, ?_⟩
  · have : 0 < Real.sqrt δ * OTDRO.Dual.quadInv A β x * M := by positivity
    linarith
  · unfold OTDRO.StrongCvx.kernelPhi
    have h := h3.second_deriv_le
      (inner ℝ β x + Real.sqrt δ * γ * OTDRO.Dual.quadInv A β x)
    have hcq : 0 < Real.sqrt δ * OTDRO.Dual.quadInv A β x := by positivity
    have := mul_le_mul_of_nonneg_left h hcq.le
    linarith
