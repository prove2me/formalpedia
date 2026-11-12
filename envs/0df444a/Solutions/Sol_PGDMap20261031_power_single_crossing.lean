-- Prove2me | solution 1 for PGDMap20261031.power_single_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T14:10:16.928557+00:00
-- url     : https://prove2.me/submissions/6b2c67f3-15a3-4e66-98be-b3852f69787d

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_PGDMap20261031_Entropy

open PGDMap20261031
noncomputable section

private def skew (c t : ℝ) : ℝ :=
  (Real.rpow (1 - t) (-c) - Real.rpow (1 + t) (-c)) /
    (Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c))

private lemma curvature_pos (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    0 < powerCurvature c t := by
  unfold powerCurvature
  exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
    (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)

private lemma skew_nonneg_mono (c₁ c₂ t : ℝ) (hc₁ : 0 ≤ c₁) (hc : c₁ ≤ c₂)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ skew c₁ t ∧ skew c₁ t ≤ skew c₂ t := by
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hbase : 1 ≤ (1 + t) / (1 - t) := by
    apply (le_div_iff₀ hminus).2
    linarith [ht.1]
  have hratio (c : ℝ) :
      Real.rpow (1 - t) (-c) / Real.rpow (1 + t) (-c) =
        Real.rpow ((1 + t) / (1 - t)) c := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hminus.le, Real.rpow_neg hplus.le,
      inv_div_inv, Real.div_rpow hplus.le hminus.le]
  have ha₁ : 0 < Real.rpow (1 - t) (-c₁) := Real.rpow_pos_of_pos hminus _
  have hb₁ : 0 < Real.rpow (1 + t) (-c₁) := Real.rpow_pos_of_pos hplus _
  have ha₂ : 0 < Real.rpow (1 - t) (-c₂) := Real.rpow_pos_of_pos hminus _
  have hb₂ : 0 < Real.rpow (1 + t) (-c₂) := Real.rpow_pos_of_pos hplus _
  have hratio₁ : 1 ≤ Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) := by
    rw [hratio]
    simpa using Real.rpow_le_rpow_of_exponent_le hbase hc₁
  have hratios : Real.rpow (1 - t) (-c₁) / Real.rpow (1 + t) (-c₁) ≤
      Real.rpow (1 - t) (-c₂) / Real.rpow (1 + t) (-c₂) := by
    rw [hratio, hratio]
    exact Real.rpow_le_rpow_of_exponent_le hbase hc
  have horder := (le_div_iff₀ hb₁).mp hratio₁
  have hcross := (div_le_div_iff₀ hb₁ hb₂).mp hratios
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · unfold skew
    apply (div_le_div_iff₀ (add_pos ha₁ hb₁) (add_pos ha₂ hb₂)).2
    nlinarith only [hcross]

private lemma curvature_hasDerivAt (c t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivAt (powerCurvature c)
      (powerCurvature c t * (c * (t + skew c t)) / (1 - t ^ 2)) t := by
  have hplus : 0 < 1 + t := by linarith [ht.1]
  have hminus : 0 < 1 - t := by linarith [ht.2]
  have hp := ((hasDerivAt_id t).const_add 1).rpow_const
    (Or.inl (ne_of_gt hplus) : 1 + t ≠ 0 ∨ 1 ≤ -c)
  have hm := ((hasDerivAt_id t).const_sub 1).rpow_const
    (Or.inl (ne_of_gt hminus) : 1 - t ≠ 0 ∨ 1 ≤ -c)
  have hsum : Real.rpow (1 - t) (-c) + Real.rpow (1 + t) (-c) ≠ 0 :=
    ne_of_gt (add_pos (Real.rpow_pos_of_pos hminus _) (Real.rpow_pos_of_pos hplus _))
  have hden : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (hp.add hm).div_const 2 using 1 <;> try rfl
  unfold powerCurvature skew
  simp only [id_eq, Real.rpow_eq_pow] at hsum ⊢
  rw [Real.rpow_sub_one (ne_of_gt hplus), Real.rpow_sub_one (ne_of_gt hminus)]
  field_simp [hsum, hden, ne_of_gt hplus, ne_of_gt hminus]
  <;> ring

private lemma ratio_hasDerivAt (c₁ c₂ t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivAt (fun t => powerCurvature c₂ t / powerCurvature c₁ t)
      ((powerCurvature c₂ t / powerCurvature c₁ t) *
        (c₂ * (t + skew c₂ t) - c₁ * (t + skew c₁ t)) / (1 - t ^ 2)) t := by
  have hk : powerCurvature c₁ t ≠ 0 := ne_of_gt (curvature_pos c₁ t ht)
  have hd : 1 - t ^ 2 ≠ 0 := ne_of_gt (by nlinarith [ht.1, ht.2])
  convert (curvature_hasDerivAt c₂ t ht).div (curvature_hasDerivAt c₁ t ht) hk using 1
    <;> try rfl
  field_simp [hk, hd]
  <;> ring

theorem solution : PowerSingleCrossingClaim := by
  intro c₁ c₂ hc₁ hc _
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro t ht
    exact (ratio_hasDerivAt c₁ c₂ t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ico] at ht
    have htco : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [(ratio_hasDerivAt c₁ c₂ t htco).deriv]
    have hskew := skew_nonneg_mono c₁ c₂ t hc₁ hc.le htco
    have hprod : c₁ * (t + skew c₁ t) < c₂ * (t + skew c₂ t) := by
      calc
        c₁ * (t + skew c₁ t) < c₂ * (t + skew c₁ t) :=
          mul_lt_mul_of_pos_right hc (by linarith [ht.1, hskew.1])
        _ ≤ c₂ * (t + skew c₂ t) :=
          mul_le_mul_of_nonneg_left (by linarith [hskew.2]) (by linarith)
    exact div_pos (mul_pos (div_pos (curvature_pos c₂ t htco) (curvature_pos c₁ t htco))
      (sub_pos.mpr hprod)) (by nlinarith [ht.1, ht.2])
