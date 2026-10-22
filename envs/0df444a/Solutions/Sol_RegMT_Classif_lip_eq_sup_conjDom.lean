-- Prove2me | solution 1 for RegMT.Classif.lip_eq_sup_conjDom
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:20:23.700522+00:00
-- url     : https://prove2.me/submissions/dfa3bf60-2739-4e24-8fcd-7f6b86617535

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
import Definitions.Def_RegMT_Classif_Model

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

namespace RMRHelp2

open WassersteinDRO.Duality

lemma slope_mem (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L) (hLip : ∃ K, LipschitzWith K L)
    (x y : ℝ) (hxy : x < y) : (L y - L x) / (y - x) ∈ RegMT.Classif.conjDom L := by
  set s : ℝ := (L y - L x) / (y - x) with hs
  have hyx : 0 < y - x := by linarith
  have hsd : L y - L x = s * (y - x) := by rw [hs]; field_simp
  obtain ⟨K, hK⟩ := hLip
  refine ⟨max (max (s * x - L x) (s * y - L y)) (|s| * (|x| + |y|) + |L x| + K * (y - x)), ?_⟩
  rintro _ ⟨z, rfl⟩
  show s * z - L z ≤ _
  rcases lt_or_ge z x with h | h
  · have := hconv.slope_mono_adjacent (Set.mem_univ z) (Set.mem_univ y) h hxy
    rw [← hs] at this
    have hzx : 0 < x - z := by linarith
    rw [div_le_iff₀ hzx] at this
    have : s * z - L z ≤ s * x - L x := by nlinarith
    exact le_trans this (le_trans (le_max_left _ _) (le_max_left _ _))
  · rcases le_or_gt z y with h2 | h2
    · have hKz := hK.dist_le_mul z x
      rw [Real.dist_eq, Real.dist_eq] at hKz
      have hzx : |z - x| ≤ y - x := by rw [abs_of_nonneg (by linarith)]; linarith
      have hKy : (K : ℝ) * |z - x| ≤ K * (y - x) := mul_le_mul_of_nonneg_left hzx K.2
      have hLz : -(L z) ≤ |L x| + K * (y - x) := by
        have h1 := neg_abs_le (L z - L x)
        have h2 := le_abs_self (L x)
        have h3 := le_abs_self (-(L x))
        rw [abs_neg] at h3
        nlinarith [abs_nonneg (L x)]
      have : s * z ≤ |s| * (|x| + |y|) := by
        calc s * z ≤ |s * z| := le_abs_self _
          _ = |s| * |z| := abs_mul _ _
          _ ≤ |s| * (|x| + |y|) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rcases abs_cases z with ⟨hz, _⟩ | ⟨hz, _⟩
            · rw [hz]; have := le_abs_self y; have := abs_nonneg x; linarith
            · rw [hz]; have := neg_abs_le x; have := abs_nonneg y; linarith
      exact le_trans (by linarith) (le_max_right _ _)
    · have := hconv.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ z) hxy h2
      have h3 : 0 < z - y := by linarith
      rw [← hs] at this
      rw [le_div_iff₀ h3] at this
      have : s * z - L z ≤ s * y - L y := by nlinarith
      exact le_trans this (le_trans (le_max_right _ _) (le_max_left _ _))

end RMRHelp2

theorem solution (L : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L) :
    WassersteinDRO.Duality.lipschitzModulus L = RegMT.Classif.conjSlope L := by
  unfold RegMT.Classif.conjSlope
  apply le_antisymm
  · unfold WassersteinDRO.Duality.lipschitzModulus
    refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
    rw [Real.norm_eq_abs]
    rcases lt_or_gt_of_ne hxy with h | h
    · have hs := RMRHelp2.slope_mem L hconv hLip x y h
      have : |L x - L y| / |x - y| = |(L y - L x) / (y - x)| := by
        rw [abs_div, abs_sub_comm (L y) (L x), abs_sub_comm y x]
      rw [this]
      exact le_iSup₂_of_le ((L y - L x) / (y - x)) hs le_rfl
    · have hs := RMRHelp2.slope_mem L hconv hLip y x h
      have : |L x - L y| / |x - y| = |(L x - L y) / (x - y)| := by
        rw [abs_div]
      rw [this]
      exact le_iSup₂_of_le ((L x - L y) / (x - y)) hs le_rfl
  · refine iSup₂_le fun θ hθ => ?_
    obtain ⟨M, hM⟩ := hθ
    have hM' : ∀ z, θ * z - L z ≤ M := fun z => hM ⟨z, rfl⟩
    have hne := RMRHelp.lipMod_ne_top L hLip
    refine ENNReal.ofReal_le_of_le_toReal ?_
    by_contra hcon
    push_neg at hcon
    set C := (WassersteinDRO.Duality.lipschitzModulus L).toReal with hC
    have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
    have hθpos : 0 < |θ| := lt_of_le_of_lt hC0 hcon
    have hδ : 0 < |θ| * (|θ| - C) := mul_pos hθpos (by linarith)
    set t : ℝ := (|M + L 0| + 1) / (|θ| * (|θ| - C)) with ht
    have htpos : 0 < t := by positivity
    have h1 := hM' (t * θ)
    have h2 := RMRHelp.abs_sub_le_C L hLip (t * θ) 0
    rw [sub_zero] at h2
    have h3 : |t * θ| = t * |θ| := by rw [abs_mul, abs_of_pos htpos]
    rw [h3] at h2
    have h4 : θ * (t * θ) = t * |θ| * |θ| := by
      have : θ * θ = |θ| * |θ| := by rw [← abs_mul_abs_self θ]
      calc θ * (t * θ) = t * (θ * θ) := by ring
        _ = t * (|θ| * |θ|) := by rw [this]
        _ = t * |θ| * |θ| := by ring
    have h5 : t * (|θ| * (|θ| - C)) = |M + L 0| + 1 := by
      rw [ht]; field_simp
    have := neg_abs_le (M + L 0)
    have := le_abs_self (M + L 0)
    nlinarith [abs_le.1 h2]
