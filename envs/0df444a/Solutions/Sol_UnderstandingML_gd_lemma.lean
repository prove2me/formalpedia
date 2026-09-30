-- Prove2me | solution 1 for UnderstandingML.gd_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:38:35.592987+00:00
-- url     : https://prove2.me/submissions/75977c74-d941-44e6-b4ba-66a606e5398b

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

/-- The telescoping identity behind Lemma 14.1. -/
lemma gd_telescope {d : ℕ} (v : ℕ → Vec d) (wstar : Vec d) (η : ℝ) (hη : 0 < η) (T : ℕ) :
    ∑ t ∈ Finset.range T, ⟪gdIterates η v t - wstar, v t⟫_ℝ =
      (‖wstar‖ ^ 2 - ‖gdIterates η v T - wstar‖ ^ 2) / (2 * η) +
        η / 2 * ∑ t ∈ Finset.range T, ‖v t‖ ^ 2 := by
  induction T with
  | zero => simp [gdIterates]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have e : gdIterates η v (T + 1) - wstar = (gdIterates η v T - wstar) - η • v T := by
      simp only [gdIterates]; abel
    rw [e, norm_sub_sq_real (gdIterates η v T - wstar) (η • v T), real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    field_simp
    ring

lemma gd_bound {d : ℕ} (v : ℕ → Vec d) (wstar : Vec d) (η : ℝ) (hη : 0 < η) (T : ℕ) :
    ∑ t ∈ Finset.range T, ⟪gdIterates η v t - wstar, v t⟫_ℝ ≤
        ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖v t‖ ^ 2 := by
  rw [gd_telescope v wstar η hη T]
  have : 0 ≤ ‖gdIterates η v T - wstar‖ ^ 2 / (2 * η) := by positivity
  rw [sub_div]; linarith

theorem solution {d : ℕ} (v : ℕ → Vec d) (T : ℕ) (wstar : Vec d) :
    (∀ η : ℝ, 0 < η →
      ∑ t ∈ Finset.range T, ⟪gdIterates η v t - wstar, v t⟫_ℝ ≤
        ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖v t‖ ^ 2) ∧
    ∀ B ρ : ℝ, 0 < B → 0 < ρ → (∀ t < T, ‖v t‖ ≤ ρ) → ‖wstar‖ ≤ B → 0 < T →
      (∑ t ∈ Finset.range T, ⟪gdIterates (B / (ρ * Real.sqrt T)) v t - wstar, v t⟫_ℝ) / T ≤
        B * ρ / Real.sqrt T := by
  refine ⟨fun η hη => gd_bound v wstar η hη T, ?_⟩
  intro B ρ hB hρ hv hw hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
  set η := B / (ρ * Real.sqrt T) with hηdef
  have hη : 0 < η := by positivity
  have h1 := gd_bound v wstar η hη T
  have hsum : ∑ t ∈ Finset.range T, ‖v t‖ ^ 2 ≤ T * ρ ^ 2 := by
    calc ∑ t ∈ Finset.range T, ‖v t‖ ^ 2 ≤ ∑ t ∈ Finset.range T, ρ ^ 2 :=
          Finset.sum_le_sum fun t ht => by
            have := hv t (Finset.mem_range.1 ht)
            exact pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = T * ρ ^ 2 := by simp
  have hw2 : ‖wstar‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  have h2 : ‖wstar‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖v t‖ ^ 2 ≤
      B ^ 2 / (2 * η) + η / 2 * (T * ρ ^ 2) := by
    gcongr
  have h3 : B ^ 2 / (2 * η) + η / 2 * (T * ρ ^ 2) = B * ρ * Real.sqrt T := by
    rw [hηdef]; generalize Real.sqrt T = s at hs hss ⊢; rw [← hss]; field_simp; ring
  rw [div_le_iff₀ hTpos]
  calc _ ≤ B * ρ * Real.sqrt T := by linarith
    _ = B * ρ / Real.sqrt T * T := by
      generalize Real.sqrt T = s at hs hss ⊢; rw [← hss]; field_simp
