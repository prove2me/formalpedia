-- Prove2me | solution 1 for OTDRO.StrongCvx.prop9_b_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:37:54.173702+00:00
-- url     : https://prove2.me/submissions/604983bb-721b-4bf0-93ad-4935b323f61c

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
theorem OTDROL8.lemma8_core {d : ℕ}
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

namespace OTDROL8

/-- first-order condition at a global maximizer -/
lemma foc (ℓ : ℝ → ℝ) (hd : Differentiable ℝ ℓ) (s c q lam γ : ℝ)
    (hmax : ∀ c' : ℝ, ℓ (s + c' * c * q) - lam * c * (c' ^ 2 * q - 1) ≤
      ℓ (s + γ * c * q) - lam * c * (γ ^ 2 * q - 1)) :
    deriv ℓ (s + γ * c * q) * (c * q) - lam * c * (2 * γ * q) = 0 := by
  have hin : HasDerivAt (fun γ : ℝ => s + γ * c * q) (c * q) γ := by
    have := (((hasDerivAt_id' γ).mul_const c).mul_const q).const_add s
    exact this.congr_deriv (by ring)
  have h1 : HasDerivAt (fun γ => ℓ (s + γ * c * q)) (deriv ℓ (s + γ * c * q) * (c * q)) γ :=
    (hd (s + γ * c * q)).hasDerivAt.comp γ hin
  have h2 : HasDerivAt (fun γ : ℝ => lam * c * (γ ^ 2 * q - 1)) (lam * c * (2 * γ * q)) γ := by
    have := (((hasDerivAt_pow 2 γ).mul_const q).sub_const 1).const_mul (lam * c)
    exact this.congr_deriv (by push_cast; ring)
  have hF := h1.sub h2
  have hloc : IsLocalMax (fun γ => ℓ (s + γ * c * q) - lam * c * (γ ^ 2 * q - 1)) γ :=
    Filter.Eventually.of_forall hmax
  exact hloc.hasDerivAt_eq_zero hF

/-- slope of `ℓ'` lies in `[0, M]` -/
lemma slope_mem (ℓ : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ ℓ) (hd : Differentiable ℝ ℓ)
    (hdd : Differentiable ℝ (deriv ℓ)) (M : ℝ) (hM : ∀ u, deriv (deriv ℓ) u ≤ M) (s u : ℝ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ ≤ M ∧ deriv ℓ (s + u) = deriv ℓ s + κ * u := by
  have hmono : Monotone (deriv ℓ) := by
    have := hc.monotoneOn_deriv (fun x _ => hd x)
    intro a b hab; exact this (Set.mem_univ a) (Set.mem_univ b) hab
  have hnn : ∀ x, 0 ≤ deriv (deriv ℓ) x := fun x => hmono.deriv_nonneg
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (deriv ℓ) x‖ ≤ M := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact hM x
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdd x) hb convex_univ
    (Set.mem_univ s) (Set.mem_univ (s + u))
  simp only [Real.norm_eq_abs, add_sub_cancel_left] at hlip
  rcases eq_or_ne u 0 with hu | hu
  · refine ⟨0, le_rfl, (hnn 0).trans (hM 0), ?_⟩
    simp [hu]
  · set κ := (deriv ℓ (s + u) - deriv ℓ s) / u
    have hκ : κ * u = deriv ℓ (s + u) - deriv ℓ s := by
      simp only [κ]; field_simp
    have hsign : 0 ≤ (deriv ℓ (s + u) - deriv ℓ s) * u := by
      rcases le_total 0 u with h | h
      · exact mul_nonneg (sub_nonneg.2 (hmono (by linarith))) h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hmono (by linarith))) h
    have hu2 : 0 < u ^ 2 := by positivity
    have hκ0 : 0 ≤ κ := by
      have : κ * u ^ 2 = (deriv ℓ (s + u) - deriv ℓ s) * u := by rw [← hκ]; ring
      by_contra hneg
      push_neg at hneg
      have : κ * u ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hu2
      linarith
    have hκM : κ ≤ M := by
      have h1 : |κ| * |u| ≤ M * |u| := by
        rw [← abs_mul, hκ]; exact hlip
      have := le_of_mul_le_mul_right h1 (abs_pos.2 hu)
      exact (le_abs_self κ).trans this
    exact ⟨κ, hκ0, hκM, by linarith⟩

end OTDROL8

open OTDROL8 in
theorem solution {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (hB : Convex ℝ B) (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ) (hL : OTDRO.StrongCvx.DerivSqBounds P0 ℓ B Llow Lbar)
    (hδ0 : δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (OTDRO.StrongCvx.Rbeta B) M) :
    ∀ᵐ x ∂P0, ∀ θ ∈ OTDRO.StrongCvx.regionW B δ M (OTDRO.StrongCvx.Rbeta B) ρmin ρmax Llow Lbar,
      θ.1 ≠ 0 →
      let g := OTDRO.StrongCvx.selectedGamma ℓ A δ θ.1 θ.2 x
      OTDRO.Dual.maximizers ℓ A δ θ.1 θ.2 x = {g} ∧
      OTDRO.StrongCvx.phiMin δ Llow ρmax (OTDRO.StrongCvx.Rbeta B) M ρmin * ‖θ.1‖ ≤
        OTDRO.StrongCvx.kernelPhi ℓ A δ g θ.1 θ.2 x ∧
      (θ ∈ OTDRO.StrongCvx.regionV B δ M (OTDRO.StrongCvx.Rbeta B) ρmin ρmax Llow Lbar →
        |deriv ℓ (inner ℝ θ.1 x)| /
          (2 * OTDRO.StrongCvx.K2 δ M (OTDRO.StrongCvx.Rbeta B) ρmin Lbar * ‖θ.1‖) ≤ |g|) ∧
      |g| ≤ |deriv ℓ (inner ℝ θ.1 x)| /
        (OTDRO.StrongCvx.phiMin δ Llow ρmax (OTDRO.StrongCvx.Rbeta B) M ρmin * ‖θ.1‖) := by
  set R := OTDRO.StrongCvx.Rbeta B with hRdef
  have hbdd : BddAbove ((fun β : EuclideanSpace ℝ (Fin d) => ‖β‖) '' B) :=
    (hB4.compact.image continuous_norm).isBounded.bddAbove
  have hnormR : ∀ β ∈ B, ‖β‖ ≤ R := fun β hβ => le_csSup hbdd ⟨β, hβ, rfl⟩
  have hρ := hA.rhoMin_pos
  have hρM := hA.rhoMax_pos
  have hM := h3.M_pos
  have hc : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hLl := hL.1
  filter_upwards [lemma8_core P0 A ρmin ρmax hA ℓ h2 δ hδ B hB M h3, hA.eig_bounds]
    with x hx hxe
  rintro θ ⟨hθB, hθ0, hθK1, hθK2⟩ hθne
  intro g
  have hβpos : 0 < ‖θ.1‖ := norm_pos_iff.2 hθne
  have hRpos : 0 < R := hβpos.trans_le (hnormR _ hθB)
  set c := Real.sqrt δ
  set q := OTDRO.Dual.quadInv A θ.1 x with hqdef
  set s := inner ℝ θ.1 x with hsdef
  have hq : 0 < q := quadInv_pos A hA.posDef θ.1 hθne x
  have hqle : q ≤ ‖θ.1‖ ^ 2 / ρmin := quadInv_le A hA.posDef θ.1 x ρmin hρ (fun v => (hxe v).1)
  have hqR : c * q * M ≤ c * R * M / ρmin * ‖θ.1‖ := by
    have : q ≤ R * ‖θ.1‖ / ρmin := by
      refine hqle.trans ?_
      apply div_le_div_of_nonneg_right _ hρ.le
      rw [sq]; exact mul_le_mul_of_nonneg_right (hnormR _ hθB) (norm_nonneg _)
    have e : c * R * M / ρmin * ‖θ.1‖ = c * M * (R * ‖θ.1‖ / ρmin) := by ring
    rw [e, show c * q * M = c * M * q by ring]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- 2 K1 = √L/√ρmax
  have h2K1 : 2 * OTDRO.StrongCvx.K1 Llow ρmax = Real.sqrt Llow / Real.sqrt ρmax := by
    unfold OTDRO.StrongCvx.K1; rw [Real.sqrt_div hLl.le]; ring
  have hphi : OTDRO.StrongCvx.phiMin δ Llow ρmax R M ρmin =
      2 * OTDRO.StrongCvx.K1 Llow ρmax - c * R * M / ρmin := by
    unfold OTDRO.StrongCvx.phiMin; rw [h2K1]
  -- key constant inequality
  have hkey : 1 / 2 * M * c * R / ρmin < OTDRO.StrongCvx.K1 Llow ρmax := by
    unfold OTDRO.StrongCvx.K1
    unfold OTDRO.StrongCvx.delta0 at hδ0
    have hx0 : 0 ≤ M * c * R / ρmin := by positivity
    have hsq : (M * c * R / ρmin) ^ 2 < Llow / ρmax := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hδ.le]
      rw [lt_div_iff₀ hρM, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at hδ0
      nlinarith
    have := (Real.lt_sqrt hx0).2 hsq
    have e : 1 / 2 * M * c * R / ρmin = 1 / 2 * (M * c * R / ρmin) := by ring
    rw [e]; linarith
  have hphipos : 0 < OTDRO.StrongCvx.phiMin δ Llow ρmax R M ρmin := by
    rw [hphi]
    have : c * R * M / ρmin = 2 * (1 / 2 * M * c * R / ρmin) := by ring
    linarith
  -- margin: 2λ − c q M ≥ φmin ‖β‖
  have hmarg : OTDRO.StrongCvx.phiMin δ Llow ρmax R M ρmin * ‖θ.1‖ ≤ 2 * θ.2 - c * q * M := by
    rw [hphi]
    have : 2 * OTDRO.StrongCvx.K1 Llow ρmax * ‖θ.1‖ ≤ 2 * θ.2 := by linarith
    nlinarith
  -- threshold
  have hthr : OTDRO.Dual.lamThr' P0 A M δ θ.1 < θ.2 := by
    have hcob : Filter.IsCoboundedUnder (· ≤ ·) (ae P0)
        (fun y => OTDRO.Dual.quadInv A θ.1 y) :=
      Filter.isCoboundedUnder_le_of_le (ae P0) (fun y => quadInv_nonneg A hA.posDef θ.1 y)
    have hE : essSup (fun y => OTDRO.Dual.quadInv A θ.1 y) P0 ≤ ‖θ.1‖ ^ 2 / ρmin := by
      apply essSup_le_of_ae_le _ _ hcob
      filter_upwards [hA.eig_bounds] with y hy
      exact quadInv_le A hA.posDef θ.1 y ρmin hρ (fun v => (hy v).1)
    unfold OTDRO.Dual.lamThr'
    have h1 : 1 / 2 * M * c * essSup (fun y => OTDRO.Dual.quadInv A θ.1 y) P0 ≤
        1 / 2 * M * c * (‖θ.1‖ ^ 2 / ρmin) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    have h2' : 1 / 2 * M * c * (‖θ.1‖ ^ 2 / ρmin) ≤ 1 / 2 * M * c * R / ρmin * ‖θ.1‖ := by
      have : ‖θ.1‖ ^ 2 ≤ R * ‖θ.1‖ := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (hnormR _ hθB) (norm_nonneg _)
      have h' : 1 / 2 * M * c * (‖θ.1‖ ^ 2 / ρmin) = (1 / 2 * M * c / ρmin) * ‖θ.1‖ ^ 2 := by
        ring
      have h'' : 1 / 2 * M * c * R / ρmin * ‖θ.1‖ = (1 / 2 * M * c / ρmin) * (R * ‖θ.1‖) := by
        ring
      rw [h', h'']
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h3' : 1 / 2 * M * c * R / ρmin * ‖θ.1‖ < OTDRO.StrongCvx.K1 Llow ρmax * ‖θ.1‖ :=
      mul_lt_mul_of_pos_right hkey hβpos
    linarith
  obtain ⟨-, -, -, ⟨γ, hγ⟩, -⟩ := hx θ.1 hθB hθne θ.2 hthr
  have hg : g = γ := by
    show sInf (OTDRO.Dual.maximizers ℓ A δ θ.1 θ.2 x) = γ
    rw [hγ, csInf_singleton]
  have hgmax : g ∈ OTDRO.Dual.maximizers ℓ A δ θ.1 θ.2 x := by rw [hγ, hg]; rfl
  have hfoc := foc ℓ h3.differentiable s c q θ.2 g hgmax
  -- 2 λ g = ℓ'(s + g c q)
  have hfoc' : deriv ℓ (s + g * c * q) = 2 * θ.2 * g := by
    have hcq : 0 < c * q := by positivity
    have : (deriv ℓ (s + g * c * q) - 2 * θ.2 * g) * (c * q) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  obtain ⟨κ, hκ0, hκM, hκ⟩ := slope_mem ℓ h2.convex h3.differentiable h3.deriv_differentiable M
    h3.second_deriv_le s (g * c * q)
  set D := 2 * θ.2 - c * q * κ with hD
  have hDeq : g * D = deriv ℓ s := by
    simp only [D]; linear_combination hκ - hfoc'
  have hDge : 2 * θ.2 - c * q * M ≤ D := by
    simp only [D]
    have := mul_le_mul_of_nonneg_left hκM (by positivity : 0 ≤ c * q); linarith
  have hDle : D ≤ 2 * θ.2 := by
    simp only [D]; have : 0 ≤ c * q * κ := by positivity
    linarith
  have hφβ : 0 < OTDRO.StrongCvx.phiMin δ Llow ρmax R M ρmin * ‖θ.1‖ :=
    mul_pos hphipos hβpos
  have hDpos : 0 < D := by linarith
  have habsg : |g| = |deriv ℓ s| / D := by
    rw [← hDeq, abs_mul, abs_of_pos hDpos, mul_div_assoc, div_self hDpos.ne', mul_one]
  refine ⟨by rw [hγ, hg], ?_, ?_, ?_⟩
  · unfold OTDRO.StrongCvx.kernelPhi
    have h := h3.second_deriv_le (s + c * g * q)
    have := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ c * q)
    linarith
  · rintro ⟨-, -, -, hV⟩
    rw [habsg]
    apply div_le_div_of_nonneg_left (abs_nonneg _) hDpos
    linarith
  · rw [habsg]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hφβ (by linarith)
