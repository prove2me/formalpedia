-- Prove2me | solution 1 for TikhonovHDD.Weak.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:30:41.529985+00:00
-- url     : https://prove2.me/submissions/a7888a86-2899-4c0f-9079-a46db34527fe

import Mathlib

set_option autoImplicit false

open Filter Topology Set

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (t₀ α : ℝ) (ht₀ : 0 < t₀) (hα : 0 < α) (u u' : ℝ → H) (ubar : H)
    (hu : ∀ t ∈ Ici t₀, HasDerivWithinAt u (u' t) (Ici t₀) t)
    (hu' : ContinuousOn u' (Ici t₀))
    (hlim : Tendsto (fun t => u t + (t / α) • u' t) atTop (𝓝 ubar)) :
    Tendsto u atTop (𝓝 ubar) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / 4 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨T₁, hT₁⟩ := (Metric.tendsto_nhds.mp hlim η hηpos).exists_forall_of_atTop
  set T : ℝ := max T₁ t₀ with hT
  have hTt₀ : t₀ ≤ T := le_max_right _ _
  have hTpos : 0 < T := lt_of_lt_of_le ht₀ hTt₀
  let g : ℝ → H := fun t => t ^ α • (u t - ubar)
  -- derivative of g
  have hg : ∀ x ∈ Ici T, HasDerivWithinAt g
      ((α * x ^ (α - 1)) • (u x + (x / α) • u' x - ubar)) (Ici x) x := by
    intro x hx
    have hxT : T ≤ x := hx
    have hxpos : 0 < x := lt_of_lt_of_le hTpos hxT
    have h1 : HasDerivWithinAt u (u' x) (Ici x) x :=
      (hu x (le_trans hTt₀ hxT)).mono (Ici_subset_Ici.mpr (le_trans hTt₀ hxT))
    have h2 : HasDerivWithinAt (fun t : ℝ => t ^ α) (α * x ^ (α - 1)) (Ici x) x :=
      (Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')).hasDerivWithinAt
    have h3 : HasDerivWithinAt g
        (x ^ α • u' x + (α * x ^ (α - 1)) • (u x - ubar)) (Ici x) x :=
      h2.smul (h1.sub_const ubar)
    refine h3.congr_deriv ?_
    have hxα : x ^ α = x * x ^ (α - 1) := by
      rw [Real.rpow_sub_one hxpos.ne']
      field_simp
    have hα0 : α ≠ 0 := hα.ne'
    have : α * x ^ (α - 1) * (x / α) = x * x ^ (α - 1) := by field_simp
    rw [smul_sub, smul_sub, smul_add, smul_smul (α * x ^ (α - 1)) (x / α), this, ← hxα]
    abel
  have hucont0 : ContinuousOn u (Ici t₀) := fun x hx => (hu x hx).continuousWithinAt
  have hucont : ContinuousOn u (Ici T) := hucont0.mono (Ici_subset_Ici.mpr hTt₀)
  have hpow : ContinuousOn (fun t : ℝ => t ^ α) (Ici T) := fun x hx =>
    (Real.continuousAt_rpow_const x α (Or.inl (lt_of_lt_of_le hTpos hx).ne')).continuousWithinAt
  have hgcont : ContinuousOn g (Ici T) := hpow.smul (hucont.sub continuousOn_const)
  -- key estimate
  have key : ∀ t ∈ Ici T, ‖g t - g T‖ ≤ η * (t ^ α - T ^ α) := by
    intro t ht
    have hTt : T ≤ t := ht
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := fun x => g x - g T) (a := T) (b := t)
      (f' := fun x => (α * x ^ (α - 1)) • (u x + (x / α) • u' x - ubar))
      (B := fun x => η * (x ^ α - T ^ α)) (B' := fun x => η * (α * x ^ (α - 1)))
      ((hgcont.mono (Icc_subset_Ici_self)).sub continuousOn_const)
      (fun x hx => (hg x hx.1).sub_const (g T))
      (by simp)
      (((hpow.mono (Icc_subset_Ici_self)).sub continuousOn_const).const_smul η)
      (fun x hx => by
        have hxpos : 0 < x := lt_of_lt_of_le hTpos hx.1
        have h2 : HasDerivWithinAt (fun t : ℝ => t ^ α) (α * x ^ (α - 1)) (Ici x) x :=
          (Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')).hasDerivWithinAt
        exact (h2.sub_const (T ^ α)).const_mul η)
      (fun x hx => by
        have hxpos : 0 < x := lt_of_lt_of_le hTpos hx.1
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := hT₁ x (le_trans (le_max_left _ _) hx.1)
        rw [dist_eq_norm] at this
        have hnn : 0 ≤ α * x ^ (α - 1) := by positivity
        calc α * x ^ (α - 1) * ‖u x + (x / α) • u' x - ubar‖
            ≤ α * x ^ (α - 1) * η := mul_le_mul_of_nonneg_left this.le hnn
          _ = η * (α * x ^ (α - 1)) := by ring)
      (x := t) ⟨hTt, le_refl _⟩
    exact this
  -- conclude
  have hpowtop : Tendsto (fun t : ℝ => t ^ α) atTop atTop := tendsto_rpow_atTop hα
  obtain ⟨T₂, hT₂⟩ := (hpowtop.eventually_ge_atTop (‖g T‖ / η)).exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop (max T T₂), eventually_gt_atTop 0] with t ht ht0
  have hTt : T ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : T₂ ≤ t := le_trans (le_max_right _ _) ht
  have hk := key t hTt
  have hbig : ‖g T‖ ≤ η * t ^ α := by
    have := hT₂ t ht2
    rw [div_le_iff₀ hηpos] at this
    linarith
  have htα : 0 < t ^ α := Real.rpow_pos_of_pos ht0 α
  have hgt : ‖g t‖ ≤ 2 * η * t ^ α := by
    have : ‖g t‖ ≤ ‖g t - g T‖ + ‖g T‖ := by have := norm_sub_norm_le (g t) (g T); linarith
    have hTα : 0 ≤ T ^ α := (Real.rpow_pos_of_pos hTpos α).le
    nlinarith
  have hnorm : ‖g t‖ = t ^ α * ‖u t - ubar‖ := by
    simp only [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htα]
  rw [hnorm] at hgt
  have : ‖u t - ubar‖ ≤ 2 * η := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [dist_eq_norm]
  rw [hη] at this
  linarith
