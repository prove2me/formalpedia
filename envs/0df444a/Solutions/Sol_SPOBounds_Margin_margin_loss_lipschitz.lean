-- Prove2me | solution 1 for SPOBounds.Margin.margin_loss_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:39:13.540865+00:00
-- url     : https://prove2.me/submissions/9a887562-f213-4cf4-a109-0f0535c8407b

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

set_option autoImplicit false

open SPOBounds.Margin in
theorem p71dfcbfc_oracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * ‖w c₁ - w c₂‖ ≤ ‖c₁ - c₂‖ := by
  have h1 := hstr c₁ (w c₂) (hw c₂).1
  have h2 := hstr c₂ (w c₁) (hw c₁).1
  have hn1 : 0 ≤ nu S c₁ := Metric.infDist_nonneg
  have hn2 : 0 ≤ nu S c₂ := Metric.infDist_nonneg
  set d := ‖w c₁ - w c₂‖ with hd
  have hd1 : ‖w c₂ - w c₁‖ = d := norm_sub_rev _ _
  rw [hd1] at h1
  have hcs : (c₁ - c₂) (w c₂ - w c₁) ≤ ‖c₁ - c₂‖ * d := by
    have := (c₁ - c₂).le_opNorm (w c₂ - w c₁)
    rw [hd1, Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have hsum : c₁ (w c₂ - w c₁) + c₂ (w c₁ - w c₂) = (c₁ - c₂) (w c₂ - w c₁) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    ring
  have hmin : min (nu S c₁) (nu S c₂) ≤ (nu S c₁ + nu S c₂) / 2 := by
    have := min_le_left (nu S c₁) (nu S c₂)
    have := min_le_right (nu S c₁) (nu S c₂)
    linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have hm0 : 0 ≤ min (nu S c₁) (nu S c₂) := le_min hn1 hn2
  have key : μ * min (nu S c₁) (nu S c₂) * d * d ≤ ‖c₁ - c₂‖ * d := by
    have e1 : μ * min (nu S c₁) (nu S c₂) * d * d ≤ μ * ((nu S c₁ + nu S c₂) / 2) * d ^ 2 := by
      have : μ * min (nu S c₁) (nu S c₂) ≤ μ * ((nu S c₁ + nu S c₂) / 2) :=
        mul_le_mul_of_nonneg_left hmin hμ.le
      nlinarith [mul_nonneg hd0 hd0]
    nlinarith
  rcases hd0.eq_or_lt with h | h
  · rw [← h]; simp
  · exact le_of_mul_le_mul_right key h

open SPOBounds.Margin in
theorem p71dfcbfc_rep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ) (hγ : 0 < γ) (chat c : StrongDual ℝ E) :
    marginLoss S w γ chat c =
      omega S c - min (nu S chat / γ) 1 * (omega S c - spoLoss w chat c) := by
  unfold marginLoss
  split_ifs with h
  · have : 1 ≤ nu S chat / γ := by rw [le_div_iff₀ hγ]; linarith
    rw [min_eq_right this]; ring
  · have : nu S chat / γ ≤ 1 := by rw [div_le_iff₀ hγ]; linarith
    rw [min_eq_left this]; ring

open SPOBounds.Margin in
theorem p71dfcbfc_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hSc : IsCompact S) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (chat c : StrongDual ℝ E) :
    0 ≤ spoLoss w chat c ∧ spoLoss w chat c ≤ omega S c := by
  have hcont : Continuous (fun v => c v) := c.continuous
  have himg : IsCompact ((fun v => c v) '' S) := hSc.image hcont
  have hb1 : BddAbove ((fun v => c v) '' S) := himg.bddAbove
  have hb2 : BddBelow ((fun v => c v) '' S) := himg.bddBelow
  have m1 : c (w chat) ∈ (fun v => c v) '' S := ⟨w chat, (hw chat).1, rfl⟩
  have m2 : c (w c) ∈ (fun v => c v) '' S := ⟨w c, (hw c).1, rfl⟩
  have s1 := le_csSup hb1 m1
  have s2 := csInf_le hb2 m2
  unfold spoLoss omega
  refine ⟨?_, ?_⟩
  · have := (hw c).2 (w chat) (hw chat).1
    linarith
  · linarith

open SPOBounds.Margin in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γ : ℝ) (hγ : 0 < γ) (c c₁ c₂ : StrongDual ℝ E) :
    |marginLoss S w γ c₁ c - marginLoss S w γ c₂ c| ≤
      (‖c‖ + μ * omega S c) / (γ * μ) * ‖c₁ - c₂‖ := by
  -- general one-sided statement, then symmetrize
  have main : ∀ a b : StrongDual ℝ E,
      min (nu S a / γ) 1 ≤ min (nu S b / γ) 1 →
      |marginLoss S w γ a c - marginLoss S w γ b c| ≤
        (‖c‖ + μ * omega S c) / (γ * μ) * ‖a - b‖ := by
    intro a b hab
    rw [p71dfcbfc_rep S w γ hγ a c, p71dfcbfc_rep S w γ hγ b c]
    set t1 := min (nu S a / γ) 1 with ht1
    set t2 := min (nu S b / γ) 1 with ht2
    set Ω := omega S c with hΩ
    set D := ‖a - b‖ with hD
    obtain ⟨ha0, ha1⟩ := p71dfcbfc_bounds S hSc w hw a c
    obtain ⟨hb0, hb1⟩ := p71dfcbfc_bounds S hSc w hw b c
    have hna : 0 ≤ nu S a := Metric.infDist_nonneg
    have hnb : 0 ≤ nu S b := Metric.infDist_nonneg
    have hD0 : 0 ≤ D := norm_nonneg _
    -- nu is 1-Lipschitz
    have hnuL : |nu S a - nu S b| ≤ D := by
      have e1 : nu S a ≤ nu S b + dist a b := Metric.infDist_le_infDist_add_dist
      have e2 : nu S b ≤ nu S a + dist b a := Metric.infDist_le_infDist_add_dist
      rw [dist_eq_norm] at e1 e2
      rw [norm_sub_rev] at e2
      rw [abs_le]; constructor <;> linarith
    have htL : |t1 - t2| ≤ D / γ := by
      have := abs_min_sub_min_le_max (nu S a / γ) 1 (nu S b / γ) 1
      rw [sub_self, abs_zero] at this
      have e : |nu S a / γ - nu S b / γ| = |nu S a - nu S b| / γ := by
        rw [← sub_div, abs_div, abs_of_pos hγ]
      have e2 : |nu S a / γ - nu S b / γ| ≤ D / γ := by
        rw [e]; exact div_le_div_of_nonneg_right hnuL hγ.le
      have e3 : max |nu S a / γ - nu S b / γ| 0 ≤ D / γ :=
        max_le e2 (div_nonneg hD0 hγ.le)
      linarith
    have ht10 : 0 ≤ t1 := le_min (div_nonneg hna hγ.le) zero_le_one
    have ht1a : t1 ≤ nu S a / γ := min_le_left _ _
    have ht1b : t1 ≤ nu S b / γ := le_trans hab (min_le_left _ _)
    have ht1m : t1 * γ ≤ min (nu S a) (nu S b) := by
      rw [le_min_iff]; constructor
      · rw [← le_div_iff₀ hγ]; exact ht1a
      · rw [← le_div_iff₀ hγ]; exact ht1b
    -- oracle bound
    have hor := p71dfcbfc_oracle S w hw μ hμ hstr a b
    set d := ‖w a - w b‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    have hspo : |spoLoss w a c - spoLoss w b c| ≤ ‖c‖ * d := by
      unfold spoLoss
      have : c (w a) - c (w c) - (c (w b) - c (w c)) = c (w a - w b) := by
        rw [map_sub]; ring
      rw [this, ← Real.norm_eq_abs]
      exact c.le_opNorm _
    -- t1 * d ≤ D / (γ μ)
    have htd : t1 * d * (γ * μ) ≤ D := by
      have : μ * (t1 * γ) * d ≤ μ * min (nu S a) (nu S b) * d := by
        apply mul_le_mul_of_nonneg_right _ hd0
        exact mul_le_mul_of_nonneg_left ht1m hμ.le
      nlinarith
    -- the decomposition
    have hdec : Ω - t1 * (Ω - spoLoss w a c) - (Ω - t2 * (Ω - spoLoss w b c)) =
        (t2 - t1) * (Ω - spoLoss w b c) + t1 * (spoLoss w a c - spoLoss w b c) := by ring
    rw [hdec]
    have hg : |Ω - spoLoss w b c| ≤ Ω := by
      rw [abs_le]; constructor <;> linarith
    have hΩ0 : 0 ≤ Ω := by linarith
    have T1 : |(t2 - t1) * (Ω - spoLoss w b c)| ≤ D / γ * Ω := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul htL hg (abs_nonneg _) (div_nonneg hD0 hγ.le)
    have T2 : |t1 * (spoLoss w a c - spoLoss w b c)| ≤ t1 * (‖c‖ * d) := by
      rw [abs_mul, abs_of_nonneg ht10]
      exact mul_le_mul_of_nonneg_left hspo ht10
    have hγμ : 0 < γ * μ := mul_pos hγ hμ
    have T2' : t1 * (‖c‖ * d) ≤ ‖c‖ * D / (γ * μ) := by
      rw [le_div_iff₀ hγμ]
      have := mul_le_mul_of_nonneg_left htd (norm_nonneg c)
      nlinarith
    have hfin : D / γ * Ω + ‖c‖ * D / (γ * μ) = (‖c‖ + μ * Ω) / (γ * μ) * D := by
      field_simp
      ring
    calc |(t2 - t1) * (Ω - spoLoss w b c) + t1 * (spoLoss w a c - spoLoss w b c)|
        ≤ |(t2 - t1) * (Ω - spoLoss w b c)| + |t1 * (spoLoss w a c - spoLoss w b c)| :=
          abs_add_le _ _
      _ ≤ D / γ * Ω + ‖c‖ * D / (γ * μ) := by linarith
      _ = (‖c‖ + μ * Ω) / (γ * μ) * D := hfin
  rcases le_total (min (nu S c₁ / γ) 1) (min (nu S c₂ / γ) 1) with h | h
  · exact main c₁ c₂ h
  · rw [abs_sub_comm, norm_sub_rev]
    exact main c₂ c₁ h
