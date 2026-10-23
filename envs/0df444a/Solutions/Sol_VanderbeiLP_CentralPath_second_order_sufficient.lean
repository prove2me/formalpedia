-- Prove2me | solution 1 for VanderbeiLP.CentralPath.second_order_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:57:57.119256+00:00
-- url     : https://prove2.me/submissions/fba34886-ceb4-4d95-9bc4-1b465e7ba522

import Mathlib

open Matrix Filter Topology


namespace VanderbeiLP.CentralPath

lemma so_taylor {n : ℕ} (f : (Fin n → ℝ) → ℝ) (xs : Fin n → ℝ)
    (hf : ∀ᶠ x in 𝓝 xs, DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (fderiv ℝ f) xs) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∀ x, ‖x - xs‖ < r →
      |f x - f xs - fderiv ℝ f xs (x - xs) -
        (1/2) * fderiv ℝ (fderiv ℝ f) xs (x - xs) (x - xs)| ≤ ε * ‖x - xs‖ ^ 2 := by
  set H := fderiv ℝ (fderiv ℝ f) xs with hHdef
  have hH : HasFDerivAt (fderiv ℝ f) H xs := hf2.hasFDerivAt
  have hsymm : ∀ v w, H v w = H w v :=
    second_derivative_symmetric_of_eventually (hf.mono fun y hy => hy.hasFDerivAt) hH
  have hlo := (hH.isLittleO).def hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hf.and hlo)
  refine ⟨r, hr, fun x hx => ?_⟩
  set ρ := ‖x - xs‖ with hρ
  let g : (Fin n → ℝ) → ℝ := fun y => f y - fderiv ℝ f xs (y - xs) - (1/2) * H (y - xs) (y - xs)
  let g' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) := fun y => fderiv ℝ f y - fderiv ℝ f xs - H (y - xs)
  have hg : ∀ y ∈ Metric.closedBall xs ρ, HasFDerivWithinAt g (g' y) (Metric.closedBall xs ρ) y := by
    intro y hy
    have hyr : dist y xs < r := by
      rw [Metric.mem_closedBall] at hy
      have : ρ < r := by simpa [dist_eq_norm] using hx
      linarith
    obtain ⟨hdf, _⟩ := hball hyr
    have h1 : HasFDerivAt f (fderiv ℝ f y) y := hdf.hasFDerivAt
    have hsub : HasFDerivAt (fun y => y - xs) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) y :=
      (hasFDerivAt_id y).sub_const xs
    have h2 : HasFDerivAt (fun y => fderiv ℝ f xs (y - xs)) (fderiv ℝ f xs) y := by
      have := (fderiv ℝ f xs).hasFDerivAt.comp y hsub
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have h3 : HasFDerivAt (fun y => H (y - xs)) H y := by
      have := H.hasFDerivAt.comp y hsub
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have h4 := h3.clm_apply hsub
    have h5 : HasFDerivAt g (fderiv ℝ f y - fderiv ℝ f xs - (1/2 : ℝ) • ((H (y - xs)).comp
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) + H.flip (y - xs))) y := by
      exact (h1.sub h2).sub (h4.const_smul (1/2 : ℝ))
    have h6 : g' y = fderiv ℝ f y - fderiv ℝ f xs - (1/2 : ℝ) • ((H (y - xs)).comp
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) + H.flip (y - xs)) := by
      ext v
      simp only [g', ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
      rw [hsymm v (y - xs)]
      try ring
    rw [h6]
    exact h5.hasFDerivWithinAt
  have hbd : ∀ y ∈ Metric.closedBall xs ρ, ‖g' y‖ ≤ ε * ρ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hyr : dist y xs < r := by
      have : ρ < r := hx
      rw [dist_eq_norm]; linarith
    obtain ⟨_, hy2⟩ := hball hyr
    calc ‖g' y‖ ≤ ε * ‖y - xs‖ := hy2
      _ ≤ ε * ρ := mul_le_mul_of_nonneg_left hy hε.le
  have := (convex_closedBall xs ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbd
    (Metric.mem_closedBall_self (norm_nonneg _)) (x := xs) (y := x)
    (by rw [Metric.mem_closedBall, dist_eq_norm])
  have hgx : g xs = f xs := by simp [g]
  have : ‖g x - g xs‖ ≤ ε * ρ * ρ := by simpa [hρ] using this
  rw [hgx] at this
  rw [Real.norm_eq_abs] at this
  have e : g x - f xs = f x - f xs - fderiv ℝ f xs (x - xs) - (1/2) * H (x - xs) (x - xs) := by
    simp only [g]; ring
  rw [e] at this
  nlinarith [this]

lemma so_negdef {n m : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)
    (H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (hhess : ∀ ξ : Fin n → ℝ, ξ ≠ 0 → (∀ i, ξ ⬝ᵥ G i = 0) → H ξ ξ < 0) :
    ∃ c > 0, ∀ ξ : Fin n → ℝ, (∀ i, ξ ⬝ᵥ G i = 0) → H ξ ξ ≤ -c * ‖ξ‖ ^ 2 := by
  let K : Set (Fin n → ℝ) := {ξ | (∀ i, ξ ⬝ᵥ G i = 0) ∧ ‖ξ‖ = 1}
  have hKc : IsCompact K := by
    have hcl : IsClosed K := by
      have : K = (⋂ i, {ξ : Fin n → ℝ | ξ ⬝ᵥ G i = 0}) ∩ {ξ | ‖ξ‖ = 1} := by
        ext; simp [K]
      rw [this]
      apply IsClosed.inter
      · refine isClosed_iInter fun i => isClosed_eq ?_ continuous_const
        simp only [dotProduct]
        fun_prop
      · exact isClosed_eq continuous_norm continuous_const
    exact Metric.isCompact_of_isClosed_isBounded hcl
      ((Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset
        (fun ξ hξ => by simp [hξ.2]))
  have hq : Continuous fun ξ : Fin n → ℝ => H ξ ξ := by
    have := H.continuous
    fun_prop
  by_cases hne : K.Nonempty
  · obtain ⟨u, huK, hu⟩ := hKc.exists_isMaxOn hne hq.continuousOn
    have hneg : H u u < 0 := hhess u (by
      intro h; have := huK.2; rw [h] at this; simp at this) huK.1
    refine ⟨-(H u u), by linarith, fun ξ hξ => ?_⟩
    by_cases hξ0 : ξ = 0
    · subst hξ0; simp
    · have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
      let v := ‖ξ‖⁻¹ • ξ
      have hvK : v ∈ K := by
        refine ⟨fun i => ?_, ?_⟩
        · simp only [v, smul_dotProduct, hξ i, smul_zero]
        · simp only [v, norm_smul, norm_inv, norm_norm]; field_simp
      have h1 : H v v ≤ H u u := hu hvK
      have h2 : H ξ ξ = ‖ξ‖ ^ 2 * H v v := by
        have : ξ = ‖ξ‖ • v := by simp only [v]; rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
        conv_lhs => rw [this]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      rw [h2]
      nlinarith [sq_nonneg ‖ξ‖]
  · refine ⟨1, one_pos, fun ξ hξ => ?_⟩
    by_cases hξ0 : ξ = 0
    · subst hξ0; simp
    · exfalso
      have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
      apply hne
      refine ⟨‖ξ‖⁻¹ • ξ, fun i => ?_, ?_⟩
      · simp only [smul_dotProduct, hξ i, smul_zero]
      · simp only [norm_smul, norm_inv, norm_norm]; field_simp

theorem so_core {m n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (G : Matrix (Fin m) (Fin n) ℝ) (β : Fin m → ℝ) (xstar : Fin n → ℝ) (y : Fin m → ℝ)
    (hf : ∀ᶠ x in 𝓝 xstar, DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (fderiv ℝ f) xstar)
    (hfeas : G *ᵥ xstar = β)
    (hcrit : ∀ v : Fin n → ℝ, fderiv ℝ f xstar v = ∑ i, y i * (G i ⬝ᵥ v))
    (hhess : ∀ ξ : Fin n → ℝ, ξ ≠ 0 → (∀ i, ξ ⬝ᵥ G i = 0) →
      fderiv ℝ (fderiv ℝ f) xstar ξ ξ < 0) :
    IsLocalMaxOn f {x | G *ᵥ x = β} xstar := by
  obtain ⟨c, hc, hcneg⟩ := so_negdef G _ hhess
  obtain ⟨r, hr, hT⟩ := so_taylor f xstar hf hf2 (c / 4) (by positivity)
  have hev : ∀ᶠ x in 𝓝 xstar, x ∈ {x | G *ᵥ x = β} → f x ≤ f xstar := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨r, hr, fun x hx hxs => ?_⟩
    have hxr : ‖x - xstar‖ < r := by simpa [dist_eq_norm] using hx
    have hker : ∀ i, (x - xstar) ⬝ᵥ G i = 0 := by
      intro i
      have : (G *ᵥ (x - xstar)) i = 0 := by
        rw [mulVec_sub]
        have h1 : G *ᵥ x = β := hxs
        simp [h1, hfeas]
      simpa [mulVec, dotProduct_comm] using this
    have h1 : fderiv ℝ f xstar (x - xstar) = 0 := by
      rw [hcrit]
      apply Finset.sum_eq_zero
      intro i _
      rw [dotProduct_comm, hker i, mul_zero]
    have h2 := hcneg _ hker
    have h3 := hT x hxr
    rw [h1] at h3
    have h4 := (abs_le.mp h3).2
    nlinarith [sq_nonneg ‖x - xstar‖]
  exact (eventually_nhdsWithin_iff.mpr hev)

end VanderbeiLP.CentralPath

open VanderbeiLP.CentralPath


theorem solution {m n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (G : Matrix (Fin m) (Fin n) ℝ) (β : Fin m → ℝ) (xstar : Fin n → ℝ) (y : Fin m → ℝ)
    (hf : ∀ᶠ x in 𝓝 xstar, DifferentiableAt ℝ f x)
    (hf2 : DifferentiableAt ℝ (fderiv ℝ f) xstar)
    (hfeas : G *ᵥ xstar = β)
    (hcrit : ∀ v : Fin n → ℝ, fderiv ℝ f xstar v = ∑ i, y i * (G i ⬝ᵥ v))
    (hhess : ∀ ξ : Fin n → ℝ, ξ ≠ 0 → (∀ i, ξ ⬝ᵥ G i = 0) →
      fderiv ℝ (fderiv ℝ f) xstar ξ ξ < 0) :
    IsLocalMaxOn f {x | G *ᵥ x = β} xstar := by
  exact so_core f G β xstar y hf hf2 hfeas hcrit hhess
