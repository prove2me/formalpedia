-- Prove2me | solution 1 for UnderstandingML.gd_convex_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:39:51.014994+00:00
-- url     : https://prove2.me/submissions/5ecd5e2c-dfd3-484b-a1bd-68d96a708247

import Theorems.Thm_UnderstandingML_gd_lemma

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

/-- A subgradient of a `ρ`-Lipschitz function has norm at most `ρ`. -/
lemma norm_le_of_isSubgradient_of_lipschitz {d : ℕ} {f : Vec d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hlip : ∀ u v, |f u - f v| ≤ ρ * ‖u - v‖) {w v : Vec d} (hv : IsSubgradient f w v) :
    ‖v‖ ≤ ρ := by
  have h1 := hv (w + v)
  have h2 := hlip (w + v) w
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1 h2
  have h3 : f (w + v) - f w ≤ ρ * ‖v‖ := le_trans (le_abs_self _) h2
  have h4 : ‖v‖ ^ 2 ≤ ρ * ‖v‖ := by linarith
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h]; exact hρ
  · nlinarith

theorem solution {d : ℕ} (f : Vec d → ℝ) (hf : ConvexOn ℝ Set.univ f) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hlip : ∀ u v, |f u - f v| ≤ ρ * ‖u - v‖) (wstar : Vec d)
    (hw : ‖wstar‖ ≤ B) (T : ℕ) (hT : 0 < T) (v : ℕ → Vec d)
    (hv : ∀ t < T, IsSubgradient f (gdIterates (B / (ρ * Real.sqrt T)) v t) (v t)) :
    f (gdAverage (B / (ρ * Real.sqrt T)) v T) - f wstar ≤ B * ρ / Real.sqrt T ∧
    ∀ ε : ℝ, 0 < ε → B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T →
      f (gdAverage (B / (ρ * Real.sqrt T)) v T) - f wstar ≤ ε := by
  set η := B / (ρ * Real.sqrt T) with hηdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  -- the directions are bounded by `ρ`
  have hvb : ∀ t < T, ‖v t‖ ≤ ρ := fun t ht =>
    norm_le_of_isSubgradient_of_lipschitz hρ.le hlip (hv t ht)
  -- Lemma 14.1
  have hgd := (UnderstandingML.gd_lemma v T wstar).2 B ρ hB hρ hvb hw hT
  -- Jensen
  have hjensen : f (gdAverage η v T) ≤ ∑ t ∈ Finset.range T, (T : ℝ)⁻¹ * f (gdIterates η v t) := by
    have := hf.map_sum_le (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹)
      (p := fun t => gdIterates η v t) (fun _ _ => by positivity)
      (by simp [Finset.card_range]; field_simp) (fun _ _ => Set.mem_univ _)
    simpa [gdAverage, Finset.smul_sum] using this
  -- subgradient inequality
  have hsub : ∀ t ∈ Finset.range T,
      f (gdIterates η v t) - f wstar ≤ ⟪gdIterates η v t - wstar, v t⟫_ℝ := by
    intro t ht
    have := hv t (Finset.mem_range.1 ht) wstar
    have e : ⟪wstar - gdIterates η v t, v t⟫_ℝ = -⟪gdIterates η v t - wstar, v t⟫_ℝ := by
      rw [← inner_neg_left, neg_sub]
    linarith
  have hmain : f (gdAverage η v T) - f wstar ≤
      (∑ t ∈ Finset.range T, ⟪gdIterates η v t - wstar, v t⟫_ℝ) / T := by
    have hsum := Finset.sum_le_sum hsub
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    rw [← Finset.mul_sum] at hjensen
    calc f (gdAverage η v T) - f wstar
        ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (gdIterates η v t) - f wstar := by linarith
      _ = (∑ t ∈ Finset.range T, f (gdIterates η v t) - T * f wstar) / T := by
          field_simp
      _ ≤ _ := by gcongr
  refine ⟨hmain.trans hgd, fun ε hε hTε => (hmain.trans hgd).trans ?_⟩
  rw [div_le_iff₀ hs]
  have : B * ρ / ε ≤ Real.sqrt T := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, mul_pow]; exact hTε
  rw [div_le_iff₀ hε] at this
  linarith
