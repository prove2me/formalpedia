-- Prove2me | solution 1 for OTDRO.Statics.maximizer_sign
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:01:02.73016+00:00
-- url     : https://prove2.me/submissions/4e11697b-20d8-4f49-b5a9-9a044ce00f88

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions
import Definitions.Def_OTDRO_Statics_Transport
import Theorems.Thm_OTDRO_StrongCvx_dual_optimizer_bounds
import Theorems.Thm_OTDRO_StrongCvx_maximizer_first_order

open MeasureTheory Matrix OTDRO.Statics

private lemma norm_le_Rβ {d : ℕ} {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB4 : OTDRO.StrongCvx.Assumption4 B) {β : EuclideanSpace ℝ (Fin d)} (hβB : β ∈ B) :
    ‖β‖ ≤ Rβ B := by
  unfold Rβ
  exact le_csSup (hB4.compact.image continuous_norm).bddAbove ⟨β, hβB, rfl⟩

private lemma phiMin_pos {ρmin ρmax Llow R M δ : ℝ}
    (hρmin : 0 < ρmin) (hρmax : 0 < ρmax) (hLlow : 0 < Llow)
    (hR : 0 < R) (hM : 0 < M) (hδ : 0 < δ)
    (hsmall : δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow R M) :
    0 < OTDRO.StrongCvx.phiMin δ Llow ρmax R M ρmin := by
  unfold OTDRO.StrongCvx.phiMin
  unfold OTDRO.StrongCvx.delta0 at hsmall
  have hden : 0 < R ^ 2 * M ^ 2 * ρmax := by positivity
  have hmul : δ * (R ^ 2 * M ^ 2 * ρmax) < ρmin ^ 2 * Llow :=
    (lt_div_iff₀ hden).mp hsmall
  have hsq : (Real.sqrt δ * R * M / ρmin) ^ 2 < (Real.sqrt Llow / Real.sqrt ρmax) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hδ.le,
      Real.sq_sqrt hLlow.le, Real.sq_sqrt hρmax.le]
    rw [div_lt_div_iff₀ (by positivity) hρmax]
    linarith
  have ha : 0 ≤ Real.sqrt δ * R * M / ρmin := by positivity
  have hb : 0 ≤ Real.sqrt Llow / Real.sqrt ρmax := by positivity
  nlinarith

private lemma quadInv_bounds {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ}
    (hPD : Q.PosDef) {ρmin : ℝ} (hρmin : 0 < ρmin)
    (heig : ∀ v : EuclideanSpace ℝ (Fin d), ρmin * ‖v‖ ^ 2 ≤ dotProduct v.ofLp (Q *ᵥ v.ofLp))
    (β : EuclideanSpace ℝ (Fin d)) :
    0 ≤ dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp) ∧
      dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp) ≤ ‖β‖ ^ 2 / ρmin := by
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Q⁻¹ *ᵥ β.ofLp)
  have hQv : Q *ᵥ v.ofLp = β.ofLp := by
    change Q *ᵥ (Q⁻¹ *ᵥ β.ofLp) = β.ofLp
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hPD.det_pos.ne'),
      Matrix.one_mulVec]
  have hq_eq : dotProduct v.ofLp (Q *ᵥ v.ofLp) = dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp) := by
    rw [hQv, dotProduct_comm]
  have hlo : ρmin * ‖v‖ ^ 2 ≤ dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp) := by
    rw [← hq_eq]
    exact heig v
  have hinner : inner ℝ β v = dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [v, dotProduct_comm]
  have hhi : dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp) ≤ ‖β‖ * ‖v‖ := by
    rw [← hinner]
    exact real_inner_le_norm β v
  refine ⟨by nlinarith [sq_nonneg ‖v‖], ?_⟩
  rw [le_div_iff₀ hρmin]
  by_cases hv : ‖v‖ = 0
  · rw [hv, mul_zero] at hhi
    nlinarith [sq_nonneg ‖β‖]
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have h1 : ρmin * ‖v‖ ≤ ‖β‖ := by nlinarith
    nlinarith [norm_nonneg β]

private lemma exists_mvt_between {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a b : ℝ) :
    ∃ η : ℝ, min a b ≤ η ∧ η ≤ max a b ∧ f b - f a = deriv f η * (b - a) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · obtain ⟨η, hη, hslope⟩ :=
      exists_deriv_eq_slope f hab hf.continuous.continuousOn hf.differentiableOn
    refine ⟨η, ?_, ?_, ?_⟩
    · simp [min_eq_left hab.le, hη.1.le]
    · simp [max_eq_right hab.le, hη.2.le]
    · rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
  · exact ⟨a, by simp, by simp, by ring⟩
  · obtain ⟨η, hη, hslope⟩ :=
      exists_deriv_eq_slope f hba hf.continuous.continuousOn hf.differentiableOn
    refine ⟨η, ?_, ?_, ?_⟩
    · simp [min_eq_right hba.le, hη.1.le]
    · simp [max_eq_left hba.le, hη.2.le]
    · have hmul : deriv f η * (a - b) = f a - f b := by
        rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hba.ne')]
      linarith

theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ)
    (hL : 0 < Llow ∧ ∀ β ∈ B,
      Llow ≤ ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ∧
      ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ≤ Lbar)
    (hsmall : δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (Rβ B) M)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hmin : IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lam)
    (G : EuclideanSpace ℝ (Fin d) → ℝ)
    (hG : ∀ᵐ x ∂P0, OTDRO.Dual.maximizers ℓ A δ β lam x = {G x}) :
    ∀ᵐ x ∂P0,
      (∃ η : ℝ,
        min (inner ℝ β x) (inner ℝ β (shiftMap A δ β G x)) ≤ η ∧
        η ≤ max (inner ℝ β x) (inner ℝ β (shiftMap A δ β G x)) ∧
        G x = deriv ℓ (inner ℝ β x) /
          (2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η) ∧
        OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖ ≤
          2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η ∧
        0 < OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖) ∧
      (0 < deriv ℓ (inner ℝ β x) → 0 < G x) ∧
      (deriv ℓ (inner ℝ β x) < 0 → G x < 0) ∧
      (deriv ℓ (inner ℝ β x) = 0 → G x = 0) := by
  have _ := hBne
  have hβ_pos : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hβ_le_R : ‖β‖ ≤ Rβ B := norm_le_Rβ hB4 hβB
  have hR_pos : 0 < Rβ B := lt_of_lt_of_le hβ_pos hβ_le_R
  have hphi_pos : 0 < OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin :=
    phiMin_pos hA.rhoMin_pos hA.rhoMax_pos hL.1 hR_pos h3.M_pos hδ hsmall
  have hphi_norm_pos : 0 < OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖ :=
    mul_pos hphi_pos hβ_pos
  have hlam_lb :=
    (OTDRO.StrongCvx.dual_optimizer_bounds P0 A ρmin ρmax hA ℓ h2 δ hδ B hB M h3 β hβB lam
      hlam hmin).1
  have h2lam : Real.sqrt Llow / Real.sqrt ρmax * ‖β‖ ≤ 2 * lam := by
    have hsqrt_ge : Real.sqrt Llow ≤ Real.sqrt (∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0) :=
      Real.sqrt_le_sqrt (hL.2 β hβB).1
    have hcoeff : 0 ≤ (1 / 2) / Real.sqrt ρmax * ‖β‖ := by positivity
    have h1 : (1 / 2) / Real.sqrt ρmax * ‖β‖ * Real.sqrt Llow ≤ lam :=
      le_trans (mul_le_mul_of_nonneg_left hsqrt_ge hcoeff) hlam_lb
    have hring : 2 * ((1 / 2) / Real.sqrt ρmax * ‖β‖ * Real.sqrt Llow) =
        Real.sqrt Llow / Real.sqrt ρmax * ‖β‖ := by ring
    linarith
  have hlam_pos : 0 < lam := by
    have hpos : 0 < Real.sqrt Llow / Real.sqrt ρmax * ‖β‖ := by
      have := hL.1
      have := hA.rhoMax_pos
      positivity
    linarith
  filter_upwards [hA.eig_bounds, hG] with x hx_eig hx_G
  have hq : 0 ≤ OTDRO.Dual.quadInv A β x ∧ OTDRO.Dual.quadInv A β x ≤ ‖β‖ ^ 2 / ρmin :=
    quadInv_bounds (hA.posDef x) hA.rhoMin_pos (fun v => (hx_eig v).1) β
  have hGx_mem : G x ∈ OTDRO.Dual.maximizers ℓ A δ β lam x := by
    rw [hx_G]
    exact Set.mem_singleton (G x)
  have hfoc : G x =
      deriv ℓ (inner ℝ β x + Real.sqrt δ * G x * OTDRO.Dual.quadInv A β x) / (2 * lam) :=
    (OTDRO.StrongCvx.maximizer_first_order P0 A ρmin ρmax hA ℓ h2 δ hδ B hB β hβB hβ x lam
      hlam_pos h3.differentiable ⟨G x, hGx_mem⟩ (G x) hGx_mem).1
  have h2lamG :
      2 * lam * G x = deriv ℓ (inner ℝ β x + Real.sqrt δ * G x * OTDRO.Dual.quadInv A β x) := by
    have hmul : G x * (2 * lam) =
        deriv ℓ (inner ℝ β x + Real.sqrt δ * G x * OTDRO.Dual.quadInv A β x) :=
      (eq_div_iff (by linarith)).mp hfoc
    linarith
  have hshift :
      inner ℝ β (shiftMap A δ β G x) =
        inner ℝ β x + Real.sqrt δ * G x * OTDRO.Dual.quadInv A β x := by
    have hinner : inner ℝ β (WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)) = OTDRO.Dual.quadInv A β x := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [OTDRO.Dual.quadInv, dotProduct_comm]
    unfold shiftMap
    rw [inner_add_right, real_inner_smul_right, hinner, mul_assoc]
  obtain ⟨η, hη_lo, hη_hi, hmvt⟩ :=
    exists_mvt_between h3.deriv_differentiable (inner ℝ β x) (inner ℝ β (shiftMap A δ β G x))
  have hD_ge : OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖ ≤
      2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η := by
    have h_term1 :
        Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η ≤
          Real.sqrt δ * OTDRO.Dual.quadInv A β x * M :=
      mul_le_mul_of_nonneg_left (h3.second_deriv_le η)
        (mul_nonneg (Real.sqrt_nonneg δ) hq.1)
    have h_term2 :
        Real.sqrt δ * OTDRO.Dual.quadInv A β x * M ≤
          Real.sqrt δ * (‖β‖ ^ 2 / ρmin) * M := by
      have hM0 : 0 ≤ M := h3.M_pos.le
      have hsq0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq.2 hsq0) hM0
    have h_term3 :
        Real.sqrt δ * (‖β‖ ^ 2 / ρmin) * M ≤
          Real.sqrt δ * Rβ B * M / ρmin * ‖β‖ := by
      have hrew : Real.sqrt δ * (‖β‖ ^ 2 / ρmin) * M =
          Real.sqrt δ * ‖β‖ * M / ρmin * ‖β‖ := by ring
      rw [hrew]
      have hM0 : 0 ≤ M := h3.M_pos.le
      have hρ0 : 0 ≤ ρmin := hA.rhoMin_pos.le
      have hsq0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
      have hβ0 : 0 ≤ ‖β‖ := hβ_pos.le
      gcongr
    unfold OTDRO.StrongCvx.phiMin
    have hring :
        (Real.sqrt Llow / Real.sqrt ρmax - Real.sqrt δ * Rβ B * M / ρmin) * ‖β‖ =
          Real.sqrt Llow / Real.sqrt ρmax * ‖β‖ - Real.sqrt δ * Rβ B * M / ρmin * ‖β‖ := by
      ring
    linarith
  have hD_pos : 0 < 2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η :=
    lt_of_lt_of_le hphi_norm_pos hD_ge
  have hDG :
      (2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η) * G x =
        deriv ℓ (inner ℝ β x) := by
    rw [hshift, ← h2lamG] at hmvt
    linear_combination hmvt
  have hGx_eq :
      G x = deriv ℓ (inner ℝ β x) /
        (2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x * deriv (deriv ℓ) η) :=
    (eq_div_iff hD_pos.ne').mpr (by rw [mul_comm]; exact hDG)
  refine ⟨⟨η, hη_lo, hη_hi, hGx_eq, hD_ge, hphi_norm_pos⟩, ?_, ?_, ?_⟩
  · intro hpos
    rw [hGx_eq]
    exact div_pos hpos hD_pos
  · intro hneg
    rw [hGx_eq]
    exact div_neg_of_neg_of_pos hneg hD_pos
  · intro hzero
    rw [hGx_eq, hzero, zero_div]
