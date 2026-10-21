-- Prove2me | solution 1 for QueueScalp.Entry.revenue_limits
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:13:09.912824+00:00
-- url     : https://prove2.me/submissions/28fcb445-3987-432e-943a-79c10a97d492

import Mathlib
import Definitions.Def_QueueScalp_Entry_Model

open QueueScalp.Entry Filter Topology

namespace QSRevLimAux

lemma f2_form (P : Params) (hS : P.Standing) (L : ℝ) (hL : 0 < L) :
    let t := Real.sqrt (L * P.V + 1)
    PiStar P L = (if L ≤ P.mu - 1 / P.V then PiStar P L else
      P.mu * P.V * (t ^ 2 - 1) * (t - 1) ^ 2 / t ^ 6) := by
  intro t
  split_ifs with h
  · rfl
  obtain ⟨hmu, hV, -⟩ := hS
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have ht2 : t ^ 2 = L * P.V + 1 := Real.sq_sqrt (by positivity)
  have ht1 : 1 < t := by
    have : 1 < L * P.V + 1 := by nlinarith
    rw [← ht2] at this; nlinarith [Real.sqrt_nonneg (L * P.V + 1)]
  have e : Real.sqrt (P.mu ^ 2 * (L * P.V + 1)) = P.mu * t := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hmu.le]
  have hLt : L = (t ^ 2 - 1) / P.V := by field_simp; linarith
  simp only [PiStar, if_neg h]
  rw [e]
  rw [show L * P.V + 1 = t ^ 2 from ht2.symm]
  rw [hLt]
  have : t ≠ 0 := by linarith
  have : P.V ≠ 0 := hV0.ne'
  have : P.mu ≠ 0 := hmu.ne'
  field_simp
  ring

lemma c1_form (P : Params) (hS : P.Standing) (L : ℝ) (hL : 0 < L) (hLm : L < P.mu) :
    (P.mu - Real.sqrt (P.mu ^ 2 - L * 1 * P.mu)) / L =
      P.mu / (P.mu + Real.sqrt (P.mu ^ 2 - L * 1 * P.mu)) := by
  obtain ⟨hmu, -, -⟩ := hS
  have hpos : 0 ≤ P.mu ^ 2 - L * 1 * P.mu := by nlinarith
  have hs := Real.sq_sqrt hpos
  have hs0 := Real.sqrt_nonneg (P.mu ^ 2 - L * 1 * P.mu)
  rw [div_eq_div_iff hL.ne' (by positivity)]
  nlinarith

end QSRevLimAux

open QSRevLimAux in
theorem solution (P : Params) (hS : P.Standing) (hk : 0 < P.k) :
    Filter.Tendsto (fun Lam : ℝ => PiStar P Lam - P.k)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-P.k)) ∧
    Filter.Tendsto (fun Lam : ℝ => PiStar P Lam - P.k)
      Filter.atTop (nhds (-P.k)) := by
  have hS' := hS
  obtain ⟨hmu, hV, -⟩ := hS'
  have hV0 : 0 < P.V := lt_trans (by positivity) hV
  have hmV : 1 < P.mu * P.V := by
    have := (div_lt_iff₀ hmu).1 hV; linarith
  have hL0 : 0 < P.mu - 1 / P.V := by
    rw [sub_pos, div_lt_iff₀ hV0]; linarith
  constructor
  · -- low demand
    set r : ℝ → ℝ := fun L => Real.sqrt (P.mu ^ 2 - L * 1 * P.mu)
    set c : ℝ → ℝ := fun L => P.mu / (P.mu + r L)
    set F : ℝ → ℝ := fun L => L ^ 3 * c L * (1 - c L) / (P.mu ^ 2 * (P.mu - L * c L))
    have hr : Continuous r := by
      exact (continuous_const.sub ((continuous_id.mul continuous_const).mul
        continuous_const)).sqrt
    have hr0 : r 0 = P.mu := by
      simp only [r]; rw [show P.mu ^ 2 - 0 * 1 * P.mu = P.mu ^ 2 by ring,
        Real.sqrt_sq hmu.le]
    have hc : ContinuousAt c 0 :=
      continuousAt_const.div (continuousAt_const.add hr.continuousAt)
        (by rw [hr0]; linarith)
    have hc0 : c 0 = 1 / 2 := by simp only [c]; rw [hr0]; field_simp; ring
    have hF : ContinuousAt F 0 := by
      apply ContinuousAt.div
      · exact ((continuousAt_id.pow 3).mul hc).mul (continuousAt_const.sub hc)
      · exact continuousAt_const.mul (continuousAt_const.sub (continuousAt_id.mul hc))
      · simp only [id, zero_mul, sub_zero]; positivity
    have hF0 : F 0 = 0 := by simp [F]
    have hlim : Tendsto F (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
      have := hF.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [hF0] at this
    have hev : F =ᶠ[𝓝[Set.Ioi 0] 0] PiStar P := by
      have hmem : Set.Ioo 0 (P.mu - 1 / P.V) ∈ 𝓝[Set.Ioi 0] 0 :=
        Ioo_mem_nhdsGT hL0
      filter_upwards [hmem] with L hL
      have hLle : L ≤ P.mu - 1 / P.V := hL.2.le
      have hLm : L < P.mu := by have : 0 < 1 / P.V := by positivity
                                linarith [hL.2]
      simp only [PiStar, ctStar, cSOf, if_pos hLle, F, c, r]
      rw [c1_form P hS L hL.1 hLm]
    have := (hlim.congr' hev).sub_const P.k
    simpa using this
  · -- high demand
    have hup : ∀ᶠ L in atTop, PiStar P L ≤ P.mu * P.V / (L * P.V + 1) := by
      filter_upwards [eventually_gt_atTop (P.mu - 1 / P.V)] with L hL
      have hL' : 0 < L := lt_trans hL0 hL
      have h := f2_form P hS L hL'
      simp only [if_neg (not_le.2 hL)] at h
      rw [h]
      set t := Real.sqrt (L * P.V + 1)
      have ht2 : t ^ 2 = L * P.V + 1 := Real.sq_sqrt (by positivity)
      have ht1 : 1 < t := by
        have : 1 < L * P.V + 1 := by nlinarith
        rw [← ht2] at this; nlinarith [Real.sqrt_nonneg (L * P.V + 1)]
      rw [← ht2, div_le_div_iff₀ (by positivity) (by positivity)]
      have hmv : 0 < P.mu * P.V := by positivity
      have h1 : (t ^ 2 - 1) * (t - 1) ^ 2 ≤ t ^ 4 := by nlinarith
      have : P.mu * P.V * (t ^ 2 - 1) * (t - 1) ^ 2 * t ^ 2 ≤ P.mu * P.V * t ^ 6 := by
        have := mul_le_mul_of_nonneg_left h1 hmv.le
        nlinarith [sq_nonneg t]
      linarith
    have hlo : ∀ᶠ L in atTop, 0 ≤ PiStar P L := by
      filter_upwards [eventually_gt_atTop (P.mu - 1 / P.V)] with L hL
      have hL' : 0 < L := lt_trans hL0 hL
      have h := f2_form P hS L hL'
      simp only [if_neg (not_le.2 hL)] at h
      rw [h]
      set t := Real.sqrt (L * P.V + 1)
      have ht2 : t ^ 2 = L * P.V + 1 := Real.sq_sqrt (by positivity)
      have ht1 : 1 < t := by
        have : 1 < L * P.V + 1 := by nlinarith
        rw [← ht2] at this; nlinarith [Real.sqrt_nonneg (L * P.V + 1)]
      have : 0 ≤ t ^ 2 - 1 := by nlinarith
      positivity
    have hg : Tendsto (fun L : ℝ => P.mu * P.V / (L * P.V + 1)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      exact tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hV0)
    have h0 : Tendsto (PiStar P) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg hlo hup
    simpa using h0.sub_const P.k
