-- Prove2me | solution 1 for UnderstandingML.ogd_regret
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:22:28.84787+00:00
-- url     : https://prove2.me/submissions/7e3ff1ac-9b26-465c-ad95-b65814733c08


import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- For a closed convex nonempty `H`, `projOnto H w` is a projection of `w` onto `H`. -/
theorem isProjection_projOnto {d : ℕ} {H : Set (Vec d)} (hHne : H.Nonempty)
    (hHc : IsClosed H) (hH : Convex ℝ H) (w : Vec d) : IsProjection H w (projOnto H w) := by
  have hex : ∃ v, IsProjection H w v := by
    obtain ⟨v, hvH, hv⟩ := exists_norm_eq_iInf_of_complete_convex hHne hHc.isComplete hH w
    refine ⟨v, hvH, fun x hx ↦ ?_⟩
    rw [norm_sub_rev v w, norm_sub_rev x w, hv]
    exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ (⟨x, hx⟩ : H)
  unfold projOnto
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- The projection lemma: projecting onto a closed convex set does not increase the distance
to any point of the set. -/
theorem norm_projOnto_sub_le {d : ℕ} {H : Set (Vec d)} (hHc : IsClosed H) (hH : Convex ℝ H)
    (w u : Vec d) (hu : u ∈ H) : ‖projOnto H w - u‖ ≤ ‖w - u‖ := by
  have hP := isProjection_projOnto ⟨u, hu⟩ hHc hH w
  set p := projOnto H w
  have hinf : ‖w - p‖ = ⨅ z : H, ‖w - z‖ := by
    apply le_antisymm
    · have : Nonempty H := ⟨⟨u, hu⟩⟩
      apply le_ciInf
      intro z
      rw [norm_sub_rev w p, norm_sub_rev w z]
      exact hP.2 z z.2
    · exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ (⟨p, hP.1⟩ : H)
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hH hP.1).1 hinf u hu
  have key : ‖w - u‖ ^ 2 = ‖w - p‖ ^ 2 - 2 * ⟪w - p, u - p⟫_ℝ + ‖u - p‖ ^ 2 := by
    have : w - u = (w - p) - (u - p) := by abel
    rw [this, norm_sub_sq_real]
  have h2 : ‖p - u‖ ^ 2 ≤ ‖w - u‖ ^ 2 := by
    rw [key, norm_sub_rev p u]
    nlinarith [sq_nonneg ‖w - p‖]
  nlinarith [norm_nonneg (p - u), norm_nonneg (w - u)]

/-- The basic OGD regret bound for a fixed step size `η > 0`. -/
theorem ogd_regret_basic {d : ℕ} (H : Set (Vec d)) (hH : Convex ℝ H) (hHc : IsClosed H)
    (f : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Vec d) (hg : ∀ t w, IsSubgradient (f t) w (g t w))
    (T : ℕ) (wstar : Vec d) (hw : wstar ∈ H) (η : ℝ) (hη : 0 < η) :
    ∑ t ∈ Finset.range T, (f t (ogdIterates H η g t) - f t wstar) ≤
      ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖g t (ogdIterates H η g t)‖ ^ 2 := by
  set W := ogdIterates H η g
  have step : ∀ t, f t (W t) - f t wstar ≤
      (‖W t - wstar‖ ^ 2 - ‖W (t + 1) - wstar‖ ^ 2) / (2 * η) + η / 2 * ‖g t (W t)‖ ^ 2 := by
    intro t
    have hsub := hg t (W t) wstar
    have hproj : ‖W (t + 1) - wstar‖ ≤ ‖W t - η • g t (W t) - wstar‖ := by
      show ‖projOnto H (W t - η • g t (W t)) - wstar‖ ≤ _
      exact norm_projOnto_sub_le hHc hH _ _ hw
    have hexp : ‖W t - η • g t (W t) - wstar‖ ^ 2 =
        ‖W t - wstar‖ ^ 2 - 2 * η * ⟪W t - wstar, g t (W t)⟫_ℝ + η ^ 2 * ‖g t (W t)‖ ^ 2 := by
      have : W t - η • g t (W t) - wstar = (W t - wstar) - η • g t (W t) := by abel
      rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    have hsq : ‖W (t + 1) - wstar‖ ^ 2 ≤ ‖W t - η • g t (W t) - wstar‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hproj 2
    have hinner : ⟪wstar - W t, g t (W t)⟫_ℝ = -⟪W t - wstar, g t (W t)⟫_ℝ := by
      rw [← inner_neg_left, neg_sub]
    rw [hinner] at hsub
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  calc ∑ t ∈ Finset.range T, (f t (W t) - f t wstar)
      ≤ ∑ t ∈ Finset.range T, ((‖W t - wstar‖ ^ 2 - ‖W (t + 1) - wstar‖ ^ 2) / (2 * η) +
          η / 2 * ‖g t (W t)‖ ^ 2) := Finset.sum_le_sum (fun t _ ↦ step t)
    _ = (‖W 0 - wstar‖ ^ 2 - ‖W T - wstar‖ ^ 2) / (2 * η) +
          η / 2 * ∑ t ∈ Finset.range T, ‖g t (W t)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub', Finset.mul_sum]
    _ ≤ ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖g t (W t)‖ ^ 2 := by
        have hW0 : W 0 = 0 := rfl
        rw [hW0, zero_sub, norm_neg]
        gcongr
        linarith [sq_nonneg ‖W T - wstar‖]

/-- A subgradient of a `ρ`-Lipschitz function has norm at most `ρ`. -/
theorem norm_subgradient_le_of_lipschitz {d : ℕ} {f : Vec d → ℝ} {ρ : NNReal}
    (hf : LipschitzWith ρ f) {w v : Vec d} (hv : IsSubgradient f w v) : ‖v‖ ≤ ρ := by
  have h1 := hv (w + v)
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1
  have h2 : f (w + v) - f w ≤ ρ * ‖v‖ := by
    have := hf.dist_le_mul (w + v) w
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
    exact le_trans (le_abs_self _) this
  have h3 : ‖v‖ ^ 2 ≤ ρ * ‖v‖ := by linarith
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h]; exact ρ.2
  · nlinarith

theorem ogd_regret {d : ℕ} (H : Set (Vec d)) (hH : Convex ℝ H) (hHc : IsClosed H)
    (f : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Vec d) (hg : ∀ t w, IsSubgradient (f t) w (g t w))
    (T : ℕ) (wstar : Vec d) (hw : wstar ∈ H) :
    (∀ η : ℝ, 0 < η →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H η g t) - f t wstar) ≤
        ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖g t (ogdIterates H η g t)‖ ^ 2) ∧
    (∀ ρ : NNReal, 0 < T → (∀ t, LipschitzWith ρ (f t)) →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H (1 / Real.sqrt T) g t) - f t wstar) ≤
        1 / 2 * (‖wstar‖ ^ 2 + (ρ : ℝ) ^ 2) * Real.sqrt T) ∧
    (∀ (ρ : NNReal) (B : ℝ), 0 < T → 0 < ρ → 0 < B → (∀ t, LipschitzWith ρ (f t)) →
      (∀ w ∈ H, ‖w‖ ≤ B) →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H (B / (ρ * Real.sqrt T)) g t) - f t wstar) ≤
        B * ρ * Real.sqrt T) := by
  have hsumρ : ∀ (ρ : NNReal), (∀ t, LipschitzWith ρ (f t)) → ∀ η : ℝ,
      ∑ t ∈ Finset.range T, ‖g t (ogdIterates H η g t)‖ ^ 2 ≤ T * (ρ : ℝ) ^ 2 := by
    intro ρ hL η
    calc ∑ t ∈ Finset.range T, ‖g t (ogdIterates H η g t)‖ ^ 2
        ≤ ∑ _t ∈ Finset.range T, (ρ : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro t _
          exact pow_le_pow_left₀ (norm_nonneg _)
            (norm_subgradient_le_of_lipschitz (hL t) (hg t _)) 2
      _ = T * (ρ : ℝ) ^ 2 := by simp
  refine ⟨fun η hη ↦ ogd_regret_basic H hH hHc f g hg T wstar hw η hη, ?_, ?_⟩
  · intro ρ hT hL
    have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
    have hss : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by positivity)
    have hb := ogd_regret_basic H hH hHc f g hg T wstar hw (1 / Real.sqrt T) (by positivity)
    have hS := hsumρ ρ hL (1 / Real.sqrt T)
    refine le_trans hb ?_
    set s := Real.sqrt T
    set S := ∑ t ∈ Finset.range T, ‖g t (ogdIterates H (1 / s) g t)‖ ^ 2
    have e1 : ‖wstar‖ ^ 2 / (2 * (1 / s)) = ‖wstar‖ ^ 2 * s / 2 := by field_simp
    have e2 : 1 / s / 2 * S ≤ 1 / s / 2 * (s ^ 2 * (ρ : ℝ) ^ 2) := by
      rw [hss]; gcongr
    have e3 : 1 / s / 2 * (s ^ 2 * (ρ : ℝ) ^ 2) = s * (ρ : ℝ) ^ 2 / 2 := by field_simp
    rw [e1]
    nlinarith
  · intro ρ B hT hρ hB hL hBd
    have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
    have hss : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by positivity)
    have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
    have hb := ogd_regret_basic H hH hHc f g hg T wstar hw (B / (ρ * Real.sqrt T))
      (by positivity)
    have hS := hsumρ ρ hL (B / (ρ * Real.sqrt T))
    refine le_trans hb ?_
    set s := Real.sqrt T
    set S := ∑ t ∈ Finset.range T, ‖g t (ogdIterates H (B / (ρ * s)) g t)‖ ^ 2
    have hw2 : ‖wstar‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBd wstar hw) 2
    have e1 : ‖wstar‖ ^ 2 / (2 * (B / (ρ * s))) ≤ B * ρ * s / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : B * ρ * s / 2 * (2 * (B / (ρ * s))) = B ^ 2 := by field_simp
      rw [this]; exact hw2
    have e2 : B / (ρ * s) / 2 * S ≤ B / (ρ * s) / 2 * (s ^ 2 * (ρ : ℝ) ^ 2) := by
      rw [hss]; gcongr
    have e3 : B / (ρ * s) / 2 * (s ^ 2 * (ρ : ℝ) ^ 2) = B * ρ * s / 2 := by field_simp
    nlinarith

end UnderstandingML

open UnderstandingML in
theorem solution {d : ℕ} (H : Set (Vec d)) (hH : Convex ℝ H) (hHc : IsClosed H)
    (f : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Vec d) (hg : ∀ t w, IsSubgradient (f t) w (g t w))
    (T : ℕ) (wstar : Vec d) (hw : wstar ∈ H) :
    (∀ η : ℝ, 0 < η →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H η g t) - f t wstar) ≤
        ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖g t (ogdIterates H η g t)‖ ^ 2) ∧
    (∀ ρ : NNReal, 0 < T → (∀ t, LipschitzWith ρ (f t)) →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H (1 / Real.sqrt T) g t) - f t wstar) ≤
        1 / 2 * (‖wstar‖ ^ 2 + (ρ : ℝ) ^ 2) * Real.sqrt T) ∧
    (∀ (ρ : NNReal) (B : ℝ), 0 < T → 0 < ρ → 0 < B → (∀ t, LipschitzWith ρ (f t)) →
      (∀ w ∈ H, ‖w‖ ≤ B) →
      ∑ t ∈ Finset.range T, (f t (ogdIterates H (B / (ρ * Real.sqrt T)) g t) - f t wstar) ≤
        B * ρ * Real.sqrt T) := by
  apply UnderstandingML.ogd_regret <;> assumption
