-- Prove2me | solution 1 for RegMT.Regress.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:05:25.163765+00:00
-- url     : https://prove2.me/submissions/63873851-f601-4220-ad46-be671f625b63

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

set_option autoImplicit false

namespace RMRHelp

open WassersteinDRO.Duality

lemma lipMod_ge (L : ℝ → ℝ) (x y : ℝ) (hxy : x ≠ y) :
    ENNReal.ofReal (|L x - L y| / |x - y|) ≤ lipschitzModulus L := by
  unfold lipschitzModulus
  refine le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy ?_))
  rw [Real.norm_eq_abs]

lemma lipMod_ne_top (L : ℝ → ℝ) (hLip : ∃ K, LipschitzWith K L) : lipschitzModulus L ≠ ⊤ := by
  obtain ⟨K, hK⟩ := hLip
  have : lipschitzModulus L ≤ (K : ENNReal) := by
    unfold lipschitzModulus
    refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
    rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal, Real.norm_eq_abs]
    have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
    rw [div_le_iff₀ hpos]
    have := hK.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq] at this
    exact this
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top this

lemma abs_sub_le_C (L : ℝ → ℝ) (hLip : ∃ K, LipschitzWith K L) (x y : ℝ) :
    |L x - L y| ≤ (lipschitzModulus L).toReal * |x - y| := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have h := lipMod_ge L x y hxy
    rw [ENNReal.ofReal_le_iff_le_toReal (lipMod_ne_top L hLip)] at h
    have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
    rwa [div_le_iff₀ hpos] at h

end RMRHelp

namespace RMRHelp3

open WassersteinDRO.Duality

lemma growth (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (x y : ℝ) (hxy : x < y) (c : ℝ)
    (hc : c < |(L y - L x) / (y - x)|) (hc0 : 0 < c) :
    ∃ σ p a : ℝ, c < a ∧ (σ = 1 ∨ σ = -1) ∧ ∀ u : ℝ, 0 ≤ u → L p + a * u ≤ L (p + σ * u) := by
  have hyx : 0 < y - x := by linarith
  rcases lt_trichotomy ((L y - L x) / (y - x)) 0 with h | h | h
  · refine ⟨-1, x, -((L y - L x) / (y - x)), ?_, Or.inr rfl, ?_⟩
    · rw [abs_of_neg h] at hc; exact hc
    · intro u hu
      rcases hu.eq_or_lt with rfl | hu'
      · simp
      · have := hconv.slope_mono_adjacent (Set.mem_univ (x + -1 * u)) (Set.mem_univ y)
          (show x + -1 * u < x by linarith) hxy
        have hu2 : 0 < x - (x + -1 * u) := by linarith
        rw [div_le_iff₀ hu2] at this
        nlinarith
  · rw [h, abs_zero] at hc; linarith
  · refine ⟨1, y, (L y - L x) / (y - x), ?_, Or.inl rfl, ?_⟩
    · rw [abs_of_pos h] at hc; exact hc
    · intro u hu
      rcases hu.eq_or_lt with rfl | hu'
      · simp
      · have := hconv.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ (y + 1 * u)) hxy
          (show y < y + 1 * u by linarith)
        have hu2 : 0 < (y + 1 * u) - y := by linarith
        rw [le_div_iff₀ hu2] at this
        nlinarith

lemma core {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (hLip : ∃ K, LipschitzWith K L)
    (β : V →L[ℝ] ℝ) (ζhat : V) (γ : ℝ) (hγ : 0 < γ)
    (hgt : γ < (lipschitzModulus L).toReal * ‖β‖) (M : ℝ) :
    ∃ ζ : V, M < L (β ζ) - γ * ‖ζ - ζhat‖ := by
  have hne := RMRHelp.lipMod_ne_top L hLip
  obtain ⟨C, hCdef⟩ : ∃ C, C = (lipschitzModulus L).toReal := ⟨_, rfl⟩
  rw [← hCdef] at hgt
  obtain ⟨nb, hnbdef⟩ : ∃ nb, nb = ‖β‖ := ⟨_, rfl⟩
  rw [← hnbdef] at hgt
  have hC0 : 0 ≤ C := by rw [hCdef]; exact ENNReal.toReal_nonneg
  have hnb0 : 0 ≤ nb := by rw [hnbdef]; exact norm_nonneg _
  have hCpos : 0 < C := by
    rcases hC0.eq_or_lt with h | h
    · rw [← h, zero_mul] at hgt; linarith
    · exact h
  have hnbpos : 0 < nb := by
    rcases hnb0.eq_or_lt with h | h
    · rw [← h, mul_zero] at hgt; linarith
    · exact h
  obtain ⟨ε, hε, hεC, hεn, hprod⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε < C ∧ ε < nb ∧ γ < (C - ε) * (nb - ε) := by
    have hδ : 0 < C * nb - γ := by linarith
    have hCn : 0 < 2 * (C + nb) := by positivity
    have hεd : (C * nb - γ) / (2 * (C + nb)) * (2 * (C + nb)) = C * nb - γ :=
      div_mul_cancel₀ _ hCn.ne'
    refine ⟨(C * nb - γ) / (2 * (C + nb)), div_pos hδ hCn, ?_, ?_, ?_⟩
    · rw [div_lt_iff₀ hCn]; nlinarith
    · rw [div_lt_iff₀ hCn]; nlinarith
    · nlinarith [sq_nonneg ((C * nb - γ) / (2 * (C + nb)))]
  have hca : 0 < C - ε := by linarith
  -- a chord with large slope
  have hlt : ENNReal.ofReal (C - ε) < lipschitzModulus L := by
    have : lipschitzModulus L = ENNReal.ofReal C := by
      rw [hCdef]; exact (ENNReal.ofReal_toReal hne).symm
    rw [this]
    exact (ENNReal.ofReal_lt_ofReal_iff hCpos).2 (by linarith)
  unfold lipschitzModulus at hlt
  simp only [lt_iSup_iff] at hlt
  obtain ⟨x, y, hxy, hxy2⟩ := hlt
  rw [Real.norm_eq_abs] at hxy2
  have hq : C - ε < |L x - L y| / |x - y| := by
    by_contra hcon
    push_neg at hcon
    exact absurd hxy2 (not_lt.2 (ENNReal.ofReal_le_ofReal hcon))
  obtain ⟨x', y', hxy', hc'⟩ : ∃ x' y', x' < y' ∧ C - ε < |(L y' - L x') / (y' - x')| := by
    rcases lt_or_gt_of_ne hxy with h | h
    · refine ⟨x, y, h, ?_⟩
      rw [abs_div, abs_sub_comm (L y) (L x), abs_sub_comm y x]
      exact hq
    · refine ⟨y, x, h, ?_⟩
      rw [abs_div]
      exact hq
  obtain ⟨σ, p, a, ha, hσ, hgrow⟩ := growth L hconv x' y' hxy' (C - ε) hc' hca
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  -- a direction in which beta is large
  have hw : ∃ w : V, (nb - ε) * ‖w‖ < β w := by
    by_contra hcon
    push_neg at hcon
    have : ‖β‖ ≤ nb - ε := by
      refine ContinuousLinearMap.opNorm_le_bound β (by linarith) fun w => ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hcon (-w)
        simp only [map_neg, norm_neg] at this
        linarith
      · exact hcon w
    linarith
  obtain ⟨w, hwb⟩ := hw
  obtain ⟨b, hb⟩ : ∃ b, b = β w := ⟨_, rfl⟩
  rw [← hb] at hwb
  have hnw : 0 ≤ ‖w‖ := norm_nonneg _
  have hb0 : 0 < b := lt_of_le_of_lt (mul_nonneg (by linarith) hnw) hwb
  have hD : 0 < a * b - γ * ‖w‖ := by
    have h1 : (C - ε) * b < a * b := mul_lt_mul_of_pos_right ha hb0
    have h2 : (C - ε) * ((nb - ε) * ‖w‖) < (C - ε) * b := mul_lt_mul_of_pos_left hwb hca
    have h3 : γ * ‖w‖ ≤ (C - ε) * (nb - ε) * ‖w‖ := mul_le_mul_of_nonneg_right hprod.le hnw
    nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D, D = a * b - γ * ‖w‖ := ⟨_, rfl⟩
  rw [← hDdef] at hD
  obtain ⟨z0, hz0⟩ : ∃ z0, z0 = β ζhat := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = L p + a * σ * (z0 - p) := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t, t = |z0 - p| / b + (|M - A0| + 1) / D := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  refine ⟨ζhat + (t * σ) • w, ?_⟩
  have hβζ : β (ζhat + (t * σ) • w) = z0 + t * σ * b := by
    rw [map_add, map_smul, smul_eq_mul, ← hz0, ← hb]
  have hnorm : ‖ζhat + (t * σ) • w - ζhat‖ = t * ‖w‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0, hσabs, mul_one]
  have htb : |z0 - p| ≤ t * b := by
    have : |z0 - p| / b * b = |z0 - p| := div_mul_cancel₀ _ hb0.ne'
    have h2 : 0 ≤ (|M - A0| + 1) / D := by positivity
    rw [htdef, add_mul]
    have : 0 ≤ (|M - A0| + 1) / D * b := by positivity
    linarith
  have hu : 0 ≤ σ * (z0 - p) + t * b := by
    have : -|z0 - p| ≤ σ * (z0 - p) := by
      have h1 := neg_abs_le (z0 - p)
      have h2 := le_abs_self (z0 - p)
      rcases hσ with rfl | rfl <;> linarith
    linarith
  have hz : β (ζhat + (t * σ) • w) = p + σ * (σ * (z0 - p) + t * b) := by
    rw [hβζ]
    linear_combination (-(z0 - p)) * hσσ
  have hg := hgrow _ hu
  rw [← hz] at hg
  rw [hnorm]
  have htD : t * D = |z0 - p| / b * D + (|M - A0| + 1) := by
    have : (|M - A0| + 1) / D * D = |M - A0| + 1 := div_mul_cancel₀ _ hD.ne'
    rw [htdef, add_mul, this]
  have h2 : 0 ≤ |z0 - p| / b * D := by positivity
  have h3 := le_abs_self (M - A0)
  have hval : L p + a * (σ * (z0 - p) + t * b) - γ * (t * ‖w‖) = A0 + t * D := by
    rw [hA0, hDdef]; ring
  nlinarith

end RMRHelp3

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (h_nonneg : ∀ z, 0 ≤ L z)
    (hLip : ∃ K, LipschitzWith K L)
    (β : V →L[ℝ] ℝ) (ζhat : V) (γ : ℝ) (hγ : 0 < γ) :
    (⨆ ζ : V, ((L (β ζ) - γ * ‖ζ - ζhat‖ : ℝ) : EReal)) =
      if WassersteinDRO.Duality.lipschitzModulus L * ENNReal.ofReal ‖β‖ ≤ ENNReal.ofReal γ then
        ((L (β ζhat) : ℝ) : EReal)
      else ⊤ := by
  have hne := RMRHelp.lipMod_ne_top L hLip
  have hC0 : 0 ≤ (WassersteinDRO.Duality.lipschitzModulus L).toReal := ENNReal.toReal_nonneg
  have hlm : WassersteinDRO.Duality.lipschitzModulus L
      = ENNReal.ofReal (WassersteinDRO.Duality.lipschitzModulus L).toReal :=
    (ENNReal.ofReal_toReal hne).symm
  have hcond : (WassersteinDRO.Duality.lipschitzModulus L * ENNReal.ofReal ‖β‖ ≤ ENNReal.ofReal γ) ↔
      (WassersteinDRO.Duality.lipschitzModulus L).toReal * ‖β‖ ≤ γ := by
    conv_lhs => rw [hlm]
    rw [← ENNReal.ofReal_mul hC0, ENNReal.ofReal_le_ofReal_iff hγ.le]
  by_cases h : (WassersteinDRO.Duality.lipschitzModulus L).toReal * ‖β‖ ≤ γ
  · rw [if_pos (hcond.2 h)]
    apply le_antisymm
    · refine iSup_le fun ζ => ?_
      refine EReal.coe_le_coe_iff.2 ?_
      have h1 := RMRHelp.abs_sub_le_C L hLip (β ζ) (β ζhat)
      have h2 : |β ζ - β ζhat| ≤ ‖β‖ * ‖ζ - ζhat‖ := by
        rw [← map_sub]
        simpa [Real.norm_eq_abs] using β.le_opNorm (ζ - ζhat)
      have h3 := mul_le_mul_of_nonneg_left h2 hC0
      have h4 := mul_le_mul_of_nonneg_right h (norm_nonneg (ζ - ζhat))
      have h5 := le_abs_self (L (β ζ) - L (β ζhat))
      nlinarith
    · exact le_iSup_of_le ζhat (by simp)
  · rw [if_neg (fun h' => h (hcond.1 h'))]
    refine iSup_eq_top.2 fun b hb => ?_
    obtain ⟨M, hbM, _⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    obtain ⟨ζ, hζ⟩ := RMRHelp3.core L hconv hLip β ζhat γ hγ (lt_of_not_ge h) M
    exact ⟨ζ, lt_trans hbM (EReal.coe_lt_coe_iff.2 hζ)⟩
