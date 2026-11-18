-- Prove2me | solution 1 for OWMR.arb_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:25.661213+00:00
-- url     : https://prove2.me/submissions/562710af-29a5-4243-b29c-aa80f16462aa

import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_renewal_depletion_mean
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_F_properties
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Real-analysis core of Lemma C.5 (case ρ > 1 - 2e/3, ρ < v ≤ e + ρ). -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace OWMR.L5aux

/-- `ψ(z) = ((1 - 4z/3)⁺)² / (8/3)`. -/
def psi (z : ℝ) : ℝ := max (1 - 4 * z / 3) 0 ^ 2 / (8 / 3)

/-- The savings cap `ḡ_e(z) = min{1, v(1-z)/ρ, (e+ρ-v+vz)/e}`. -/
def gb (e ρ v z : ℝ) : ℝ := min 1 (min (v * (1 - z) / ρ) ((e + ρ - v + v * z) / e))

lemma psi_nonneg (z : ℝ) : 0 ≤ psi z := by unfold psi; positivity

lemma psi_le (z : ℝ) (hz : 0 ≤ z) : psi z ≤ 3 / 8 := by
  unfold psi
  have h1 : max (1 - 4 * z / 3) 0 ≤ 1 := max_le (by linarith) zero_le_one
  have h0 : 0 ≤ max (1 - 4 * z / 3) 0 := le_max_right _ _
  have : max (1 - 4 * z / 3) 0 ^ 2 ≤ 1 := by nlinarith
  linarith [show max (1 - 4 * z / 3) 0 ^ 2 / (8 / 3) = 3 / 8 * max (1 - 4 * z / 3) 0 ^ 2 by ring]

lemma psi_of_le (z : ℝ) (hz : z ≤ 3 / 4) : psi z = 3 / 8 * (1 - 4 * z / 3) ^ 2 := by
  unfold psi; rw [max_eq_left (by linarith)]; ring

/-- Chord bound for `ψ` on `[z1, 1]` (it vanishes at `1`). -/
lemma psi_chord (z1 z : ℝ) (hz1 : 0 ≤ z1) (hz13 : z1 ≤ 3 / 4) (hz : z1 ≤ z) (hz1' : z ≤ 1) :
    psi z * (1 - z1) ≤ (1 - z) * psi z1 := by
  rw [psi_of_le z1 hz13]
  rcases le_or_gt z (3 / 4) with hz3 | hz3
  · rw [psi_of_le z hz3]
    set a := 1 - 4 * z / 3 with ha
    set b := 1 - 4 * z1 / 3 with hb
    have ha0 : 0 ≤ a := by linarith
    have hab : a ≤ b := by linarith
    have e1 : 1 - z1 = (1 + 3 * b) / 4 := by rw [hb]; ring
    have e2 : 1 - z = (1 + 3 * a) / 4 := by rw [ha]; ring
    rw [e1, e2]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (add_nonneg (add_nonneg ha0 (ha0.trans hab))
      (mul_nonneg (mul_nonneg ha0 (ha0.trans hab)) (by norm_num : (0:ℝ) ≤ 3)))]
  · have : psi z = 0 := by unfold psi; rw [max_eq_right (by linarith)]; ring
    rw [this, zero_mul]
    exact mul_nonneg (by linarith) (by positivity)

lemma core (e ρ v z : ℝ) (he0 : 0 < e) (he1 : e ≤ 1) (hρ1 : ρ ≤ 1) (hρe : 1 - 2 * e / 3 < ρ)
    (hvρ : ρ < v) (hve : v ≤ e + ρ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    v * (3 * z / 4 + 2 * psi z) + 7 * e / 12 * gb e ρ v z + v / 8
        + 3 * v * (1 - ρ) / (8 * (1 + ρ)) ≤ 7 * (1 + e) / 8 := by
  have hρ3 : 1 / 3 < ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hv0 : 0 < v := by linarith
  have hρp : 0 < 1 + ρ := by linarith
  obtain ⟨z1, hz1def⟩ : ∃ z1 : ℝ, z1 = 1 - ρ / v := ⟨_, rfl⟩
  have hvz1 : v * z1 = v - ρ := by rw [hz1def]; field_simp
  have hz1_0 : 0 ≤ z1 := by
    rw [hz1def, sub_nonneg, div_le_one hv0]; linarith
  have hz1_34 : z1 ≤ 3 / 4 := by
    rw [hz1def]
    have : 1 / 4 ≤ ρ / v := by rw [le_div_iff₀ hv0]; linarith
    linarith
  have hz1_1 : z1 < 1 := by
    rw [hz1def]; have : 0 < ρ / v := div_pos hρ0 hv0
    linarith
  have hg_lo : ∀ z, 0 ≤ z → z ≤ z1 → 7 * e / 12 * gb e ρ v z = 7 * (e + ρ - v + v * z) / 12 := by
    intro z hz hzz
    have hvz : v * z ≤ v - ρ := by rw [← hvz1]; exact mul_le_mul_of_nonneg_left hzz hv0.le
    unfold gb
    have h3 : (e + ρ - v + v * z) / e ≤ 1 := by rw [div_le_one he0]; linarith
    have h2 : 1 ≤ v * (1 - z) / ρ := by rw [le_div_iff₀ hρ0]; linarith
    rw [min_eq_right (le_trans h3 h2), min_eq_right h3]
    field_simp
  have hg_hi : ∀ z, z1 ≤ z → z ≤ 1 →
      7 * e / 12 * gb e ρ v z = 7 * e * (1 - z) / (12 * (1 - z1)) := by
    intro z hz hzz
    have hvz : v - ρ ≤ v * z := by rw [← hvz1]; exact mul_le_mul_of_nonneg_left hz hv0.le
    unfold gb
    have h2 : v * (1 - z) / ρ ≤ 1 := by rw [div_le_one hρ0]; linarith
    have h3 : 1 ≤ (e + ρ - v + v * z) / e := by rw [le_div_iff₀ he0]; linarith
    rw [min_eq_left (le_trans h2 h3), min_eq_right h2]
    have : 1 - z1 = ρ / v := by rw [hz1def]; ring
    rw [this]; field_simp
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = v / 8 + 3 * v * (1 - ρ) / (8 * (1 + ρ)) := ⟨_, rfl⟩
  have hgoal : v * (3 * z / 4 + 2 * psi z) + 7 * e / 12 * gb e ρ v z + v / 8
      + 3 * v * (1 - ρ) / (8 * (1 + ρ))
      = v * (3 * z / 4 + 2 * psi z) + 7 * e / 12 * gb e ρ v z + c := by
    rw [hc]; ring
  rw [hgoal]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 7 * (1 + e) / 8 := ⟨_, rfl⟩
  rw [← hC]
  have hA : (e + ρ) * (5 + 2 * ρ) / (4 * (1 + ρ)) ≤ C := by
    rw [hC, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (by linarith : (0:ℝ) ≤ 4 * ρ + 7 - 3 * e)]
  have hE0 : 3 * v / 4 + 7 * (e + ρ - v) / 12 + c ≤ C := by
    have key : 3 * v / 4 + 7 * (e + ρ - v) / 12 + c
        = v * (8 - ρ) / (12 * (1 + ρ)) + 7 * (e + ρ) / 12 := by
      rw [hc]; field_simp; ring
    have h1 : v * (8 - ρ) / (12 * (1 + ρ)) ≤ (e + ρ) * (8 - ρ) / (12 * (1 + ρ)) := by
      gcongr <;> linarith
    have h2 : (e + ρ) * (8 - ρ) / (12 * (1 + ρ)) + 7 * (e + ρ) / 12
        = (e + ρ) * (5 + 2 * ρ) / (4 * (1 + ρ)) := by field_simp; ring
    linarith
  have hE1 : 3 * v / 4 + c ≤ C := by
    have key : 3 * v / 4 + c = v * (5 + 2 * ρ) / (4 * (1 + ρ)) := by
      rw [hc]; field_simp; ring
    have h1 : v * (5 + 2 * ρ) / (4 * (1 + ρ)) ≤ (e + ρ) * (5 + 2 * ρ) / (4 * (1 + ρ)) := by
      gcongr <;> linarith
    linarith
  have hPv : (32 + 14 * ρ) * v ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * v + 32 * ρ ^ 2 * (1 + ρ)
      ≤ 0 := by
    have hPρ : (32 + 14 * ρ) * ρ ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * ρ
        + 32 * ρ ^ 2 * (1 + ρ) ≤ 0 := by
      have e1 : (32 + 14 * ρ) * ρ ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * ρ
          + 32 * ρ ^ 2 * (1 + ρ) = ρ * (3 * (ρ - 1) * (4 * ρ + 7) - 7 * e * (1 + ρ)) := by ring
      rw [e1]
      refine mul_nonpos_of_nonneg_of_nonpos hρ0.le ?_
      have : 0 ≤ 3 * (1 - ρ) * (4 * ρ + 7) :=
        mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.2 hρ1)) (by linarith)
      nlinarith
    have hPe : (32 + 14 * ρ) * (e + ρ) ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * (e + ρ)
        + 32 * ρ ^ 2 * (1 + ρ) ≤ 0 := by
      have q0 : 0 ≤ 3 * ρ * (1 - ρ) * (4 * ρ + 7) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0.le) (sub_nonneg.2 hρ1)) (by linarith)
      have q1 : 0 ≤ 4 * (3 * ρ - 1) * (1 - ρ) * (ρ + 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sub_nonneg.2 hρ1))
          (by linarith)
      have hid : (32 + 14 * ρ) * (e + ρ) ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * (e + ρ)
          + 32 * ρ ^ 2 * (1 + ρ)
          = -((1 - e) * (3 * ρ * (1 - ρ) * (4 * ρ + 7)))
            - e * (4 * (3 * ρ - 1) * (1 - ρ) * (ρ + 1)) - (25 + 7 * ρ) * e * (1 - e) := by ring
      rw [hid]
      have a1 := mul_nonneg (sub_nonneg.2 he1) q0
      have a2 := mul_nonneg he0.le q1
      have a3 : 0 ≤ (25 + 7 * ρ) * e * (1 - e) :=
        mul_nonneg (mul_nonneg (by linarith) he0.le) (sub_nonneg.2 he1)
      linarith
    have hid : e * ((32 + 14 * ρ) * v ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * v
        + 32 * ρ ^ 2 * (1 + ρ))
        = (e + ρ - v) * ((32 + 14 * ρ) * ρ ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * ρ
            + 32 * ρ ^ 2 * (1 + ρ))
          + (v - ρ) * ((32 + 14 * ρ) * (e + ρ) ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * (e + ρ)
            + 32 * ρ ^ 2 * (1 + ρ))
          - e * (32 + 14 * ρ) * (v - ρ) * (e + ρ - v) := by ring
    have b1 := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ e + ρ - v) hPρ
    have b2 := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ v - ρ) hPe
    have b3 : 0 ≤ e * (32 + 14 * ρ) * (v - ρ) * (e + ρ - v) :=
      mul_nonneg (mul_nonneg (mul_nonneg he0.le (by linarith)) (by linarith)) (by linarith)
    have h4 : e * ((32 + 14 * ρ) * v ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * v
        + 32 * ρ ^ 2 * (1 + ρ)) ≤ 0 := by rw [hid]; linarith
    by_contra hcon
    rw [not_le] at hcon
    have := mul_pos he0 hcon
    linarith
  have hEm : 3 * (v - ρ) / 4 + (4 * ρ - v) ^ 2 / (12 * v) + 7 * e / 12 + c ≤ C := by
    have key : 3 * (v - ρ) / 4 + (4 * ρ - v) ^ 2 / (12 * v) + 7 * e / 12 + c - C
        = ((32 + 14 * ρ) * v ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * v + 32 * ρ ^ 2 * (1 + ρ))
          / (24 * v * (1 + ρ)) := by
      rw [hc, hC]; field_simp; ring
    have : ((32 + 14 * ρ) * v ^ 2 - (1 + ρ) * (34 * ρ + 21 + 7 * e) * v + 32 * ρ ^ 2 * (1 + ρ))
        / (24 * v * (1 + ρ)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hPv (by positivity)
    linarith
  have hpsim : v * psi z1 = (4 * ρ - v) ^ 2 / (24 * v) := by
    rw [psi_of_le z1 hz1_34, hz1def]; field_simp; ring
  rcases le_or_gt z z1 with hzz | hzz
  · rw [hg_lo z hz0 hzz, psi_of_le z (hzz.trans hz1_34)]
    rcases eq_or_lt_of_le hz1_0 with h0 | h0
    · have hz : z = 0 := le_antisymm (h0 ▸ hzz) hz0
      subst hz
      have : v * (3 * 0 / 4 + 2 * (3 / 8 * (1 - 4 * 0 / 3) ^ 2)) + 7 * (e + ρ - v + v * 0) / 12 + c
          = 3 * v / 4 + 7 * (e + ρ - v) / 12 + c := by ring
      linarith
    · have hchord : z1 * (v * (3 * z / 4 + 2 * (3 / 8 * (1 - 4 * z / 3) ^ 2))
            + 7 * (e + ρ - v + v * z) / 12 + c)
          = (z1 - z) * (3 * v / 4 + 7 * (e + ρ - v) / 12 + c)
            + z * (3 * (v * z1) / 4 + 2 * (v * (3 / 8 * (1 - 4 * z1 / 3) ^ 2))
              + 7 * (e + ρ - v + v * z1) / 12 + c)
            - 4 * v / 3 * z1 * z * (z1 - z) := by ring
      have hfz1 : 3 * (v * z1) / 4 + 2 * (v * (3 / 8 * (1 - 4 * z1 / 3) ^ 2))
            + 7 * (e + ρ - v + v * z1) / 12 + c
          = 3 * (v - ρ) / 4 + (4 * ρ - v) ^ 2 / (12 * v) + 7 * e / 12 + c := by
        rw [← psi_of_le z1 hz1_34, hpsim, hvz1]; field_simp; ring
      have hpos : 0 ≤ 4 * v / 3 * z1 * z * (z1 - z) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hz1_0) hz0) (sub_nonneg.2 hzz)
      have : z1 * (v * (3 * z / 4 + 2 * (3 / 8 * (1 - 4 * z / 3) ^ 2))
            + 7 * (e + ρ - v + v * z) / 12 + c) ≤ z1 * C := by
        rw [hchord, hfz1]
        have h3 := mul_le_mul_of_nonneg_left hE0 (sub_nonneg.2 hzz)
        have h4 := mul_le_mul_of_nonneg_left hEm hz0
        linarith [h3, h4, hpos]
      exact le_of_mul_le_mul_left this h0
  · rw [hg_hi z hzz.le hz1]
    have hch := psi_chord z1 z hz1_0 hz1_34 hzz.le hz1
    have h1z1 : 0 < 1 - z1 := by linarith
    have hfm : v * (3 * z1 / 4 + 2 * psi z1) + 7 * e / 12 + c ≤ C := by
      have : v * (3 * z1 / 4 + 2 * psi z1) + 7 * e / 12 + c
          = 3 * (v - ρ) / 4 + (4 * ρ - v) ^ 2 / (12 * v) + 7 * e / 12 + c := by
        have h1 : v * (3 * z1 / 4 + 2 * psi z1) = 3 * (v * z1) / 4 + 2 * (v * psi z1) := by ring
        rw [h1, hpsim, hvz1]; field_simp; ring
      linarith
    have e1 : (1 - z1) * (7 * e * (1 - z) / (12 * (1 - z1))) = 7 * e * (1 - z) / 12 := by
      field_simp
    have hkey : (1 - z1) * (v * (3 * z / 4 + 2 * psi z) + 7 * e * (1 - z) / (12 * (1 - z1)) + c)
        ≤ (1 - z) * (v * (3 * z1 / 4 + 2 * psi z1) + 7 * e / 12 + c)
          + (z - z1) * (3 * v / 4 + c) := by
      have : (1 - z1) * (v * (3 * z / 4 + 2 * psi z) + 7 * e * (1 - z) / (12 * (1 - z1)) + c)
          = (1 - z1) * (3 * v * z / 4) + 2 * v * (psi z * (1 - z1)) + 7 * e * (1 - z) / 12
            + (1 - z1) * c := by
        rw [← e1]; ring
      rw [this]
      have h2 : 2 * v * (psi z * (1 - z1)) ≤ 2 * v * ((1 - z) * psi z1) :=
        mul_le_mul_of_nonneg_left hch (by linarith)
      linarith [h2]
    have : (1 - z1) * (v * (3 * z / 4 + 2 * psi z) + 7 * e * (1 - z) / (12 * (1 - z1)) + c)
        ≤ (1 - z1) * C := by
      refine hkey.trans ?_
      have h3 := mul_le_mul_of_nonneg_left hfm (by linarith : (0:ℝ) ≤ 1 - z)
      have h4 := mul_le_mul_of_nonneg_left hE1 (by linarith : (0:ℝ) ≤ z - z1)
      linarith [h3, h4]
    exact le_of_mul_le_mul_left this h1z1

end OWMR.L5aux

namespace OWMR.L5aux

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ =>
    (measurable_pi_apply j).coe_nnreal_real) measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma gb_le_one (e ρ v z : ℝ) : gb e ρ v z ≤ 1 := min_le_left _ _

lemma gb_nonneg (e ρ v z : ℝ) (he : 0 < e) (hρ : 0 < ρ) (hv : 0 ≤ v) (hve : v ≤ e + ρ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ gb e ρ v z := by
  unfold gb
  refine le_min zero_le_one (le_min (div_nonneg (mul_nonneg hv (by linarith)) hρ.le)
    (div_nonneg ?_ he.le))
  nlinarith [mul_nonneg hv hz0]

end OWMR.L5aux

set_option maxHeartbeats 4000000 in
open OWMR.L5aux in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) (m : ℝ)
    (hm : 1 ≤ m) (hH : m * N.h ≤ N.H i) (hp : N.h ≤ N.p) (k sh Sh : ℝ) (hk : 0 < k)
    (hc : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh) :
    N.h * (∫ x in Set.Ico 0 (Sh - sh), x ∂(renewalMeasure (N.marginal i)))
        / (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal
      + min (N.h * (3 / 8) * (Sh - sh))
          ((N.h + N.p) * (Sh - sh)
            * (∫ x in Set.Ico 0 (Sh - sh), max (1 - 4 * (x / (Sh - sh)) / 3) 0 ^ 2 / (8 / 3)
                ∂(renewalMeasure (N.marginal i)))
            / (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal)
      ≤ 7 / 8 * (1 + 1 / m) * (N.J i k).toReal
        - 7 / (12 * m) * k / (renewalMeasure (N.marginal i) (Set.Ico 0 (Sh - sh))).toReal := by
  obtain ⟨hsS, hopt, hfs, hfS, hfI⟩ := hc
  have hh : 0 < N.h := hN.h_pos
  have hHp : 0 < N.H i := hN.H_pos i
  have hpp : 0 < N.p := hN.p_pos
  set ρi := N.marginal i with hρi
  set U := renewalMeasure ρi with hU
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Sh - sh := ⟨_, rfl⟩
  rw [← hw]
  have hw0 : 0 < w := by rw [hw]; linarith
  have hmean : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρi := by
    rw [hρi]; unfold Network.marginal
    rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
    exact hN.mean_pos i
  have hUe_top : U (Set.Ico 0 w) ≠ ∞ := (renewalMeasure_Ico_lt_top ρi hmean w).ne
  have hUe_one : 1 ≤ U (Set.Ico 0 w) := one_le_renewal ρi w hw0
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (U (Set.Ico 0 w)).toReal := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : 1 ≤ M := by
    rw [hM]; have := ENNReal.toReal_mono hUe_top hUe_one; simpa using this
  have hM0 : 0 < M := by linarith
  -- properties of `F`
  obtain ⟨hF0, -, hFlip, hFslope⟩ := F_properties N hN i
  have hFc : Continuous (N.F i) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine Metric.continuousAt_iff.2 fun ε hε => ⟨ε / (N.H i + N.p + 1), by positivity, fun y' hy' => ?_⟩
    rw [Real.dist_eq] at hy' ⊢
    have := hFlip y' y
    calc |N.F i y' - N.F i y| ≤ (N.H i + N.p) * |y' - y| := this
      _ ≤ (N.H i + N.p) * (ε / (N.H i + N.p + 1)) := by gcongr
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  -- the value
  have hss := ss_renewal_reward ρi hmean (N.F i) hFc.measurable hF0 k sh Sh hk.le hsS
    ⟨N.F i sh + (N.H i + N.p) * (Sh - sh), fun y hy => by
      have := hFlip y sh
      rw [abs_le] at this
      have h2 : |y - sh| ≤ Sh - sh := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      nlinarith [abs_nonneg (y - sh), mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ N.H i + N.p)]⟩
  rw [← hw, ← hU] at hss
  set IF := ∫ x in Set.Ico 0 w, N.F i (Sh - x) ∂U with hIF
  have hIF0 : 0 ≤ IF := setIntegral_nonneg measurableSet_Ico fun x _ => hF0 _
  have hJdef : N.J i k = slValue ρi (N.F i) k := rfl
  have hJ : N.J i k = ENNReal.ofReal ((k + IF) / M) := by
    rw [hJdef, ← hopt, hss, hM]
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (N.J i k).toReal := ⟨_, rfl⟩
  rw [← hG]
  have hGv : G = (k + IF) / M := by
    rw [hG, hJ, ENNReal.toReal_ofReal (div_nonneg (by linarith) hM0.le)]
  have hG0 : 0 < G := by rw [hGv]; positivity
  have hJG : N.J i k = ENNReal.ofReal G := by rw [hJ, hGv]
  have hFs : N.F i sh = G := by
    have := hfs; rw [← hJdef, hJG] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (hF0 _) hG0.le).1 this
  have hFS : N.F i Sh ≤ G := by
    have := hfS; rw [← hJdef, hJG] at this
    exact (ENNReal.ofReal_le_ofReal_iff hG0.le).1 this
  have hFI : ∀ y ∈ Set.Icc sh Sh, N.F i y ≤ G := by
    intro y hy
    have := hfI y hy; rw [← hJdef, hJG] at this
    exact (ENNReal.ofReal_le_ofReal_iff hG0.le).1 this
  -- Jensen bounds at the endpoints
  set π := Measure.pi fun _ : Fin (N.L i + 1) => ρi with hπ
  set μZ := ∫ z, ∑ j, (z j : ℝ) ∂π with hμZ
  have hint_m : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρi := by
    rw [hρi]; unfold Network.marginal
    rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable]
    have h := integrable_toReal_of_lintegral_ne_top
      (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
      ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
    simpa [Function.comp_def] using h
  have hu : Integrable (fun z : Fin (N.L i + 1) → ℝ≥0 => ∑ j, (z j : ℝ)) π := by
    refine integrable_finsetSum _ fun j _ => ?_
    have hmp := measurePreserving_eval (μ := fun _ : Fin (N.L i + 1) => ρi) j
    exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 hint_m
  have hφ : ∀ y, Integrable (fun z : Fin (N.L i + 1) → ℝ≥0 =>
      N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0) π := fun y =>
    (((integrable_const y).sub hu).pos_part.const_mul _).add
      ((hu.sub (integrable_const y)).pos_part.const_mul _)
  have hFdef : ∀ y, N.F i y = ∫ z, (N.H i * max (y - ∑ j, (z j : ℝ)) 0
      + N.p * max (∑ j, (z j : ℝ) - y) 0) ∂π := fun y => rfl
  have hlow1 : ∀ y, N.p * (μZ - y) ≤ N.F i y := by
    intro y
    have e : ∫ z, N.p * (∑ j, (z j : ℝ) - y) ∂π = N.p * (μZ - y) := by
      rw [integral_const_mul, integral_sub hu (integrable_const y), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl
    rw [← e, hFdef]
    refine integral_mono ((hu.sub (integrable_const y)).const_mul _) (hφ y) fun z => ?_
    have h1 : 0 ≤ N.H i * max (y - ∑ j, (z j : ℝ)) 0 := mul_nonneg hHp.le (le_max_right _ _)
    have h2 : N.p * (∑ j, (z j : ℝ) - y) ≤ N.p * max (∑ j, (z j : ℝ) - y) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hpp.le
    simp only
    linarith
  have hlow2 : ∀ y, N.H i * (y - μZ) ≤ N.F i y := by
    intro y
    have e : ∫ z, N.H i * (y - ∑ j, (z j : ℝ)) ∂π = N.H i * (y - μZ) := by
      rw [integral_const_mul, integral_sub (integrable_const y) hu, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl
    rw [← e, hFdef]
    refine integral_mono (((integrable_const y).sub hu).const_mul _) (hφ y) fun z => ?_
    have h1 : 0 ≤ N.p * max (∑ j, (z j : ℝ) - y) 0 := mul_nonneg hpp.le (le_max_right _ _)
    have h2 : N.H i * (y - ∑ j, (z j : ℝ)) ≤ N.H i * max (y - ∑ j, (z j : ℝ)) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hHp.le
    simp only
    linarith
  -- slope of `F` at most `H`
  have hslopeH : ∀ x, 0 ≤ x → N.F i Sh - N.H i * x ≤ N.F i (Sh - x) := by
    intro x hx
    have e : N.F i Sh - N.H i * x = ∫ z, (N.H i * max (Sh - ∑ j, (z j : ℝ)) 0
        + N.p * max (∑ j, (z j : ℝ) - Sh) 0 - N.H i * x) ∂π := by
      rw [integral_sub (hφ Sh) (integrable_const _), integral_const, hFdef]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [e, hFdef]
    refine integral_mono ((hφ Sh).sub (integrable_const _)) (hφ (Sh - x)) fun z => ?_
    simp only
    have a1 : max (Sh - ∑ j, (z j : ℝ)) 0 - x ≤ max (Sh - x - ∑ j, (z j : ℝ)) 0 := by
      rcases le_total (Sh - ∑ j, (z j : ℝ)) 0 with h | h
      · rw [max_eq_right h]; linarith [le_max_right (Sh - x - ∑ j, (z j : ℝ)) 0]
      · rw [max_eq_left h]
        have := le_max_left (Sh - x - ∑ j, (z j : ℝ)) 0
        linarith
    have a2 : max (∑ j, (z j : ℝ) - Sh) 0 ≤ max (∑ j, (z j : ℝ) - (Sh - x)) 0 :=
      max_le_max (by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left a1 hHp.le, mul_le_mul_of_nonneg_left a2 hpp.le]
  have hpHw : N.p * N.H i * w ≤ N.H i * G + N.p * N.F i Sh := by
    have a1 := hlow1 sh
    have a2 := hlow2 Sh
    rw [hFs] at a1
    have := mul_le_mul_of_nonneg_left a1 hHp.le
    have := mul_le_mul_of_nonneg_left a2 hpp.le
    rw [hw]; nlinarith
  -- parameters
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 / m := ⟨_, rfl⟩
  have hm0 : 0 < m := by linarith
  have he0 : 0 < e := by rw [he]; positivity
  have he1 : e ≤ 1 := by rw [he, div_le_one hm0]; exact hm
  obtain ⟨rr, hrr⟩ : ∃ rr : ℝ, rr = N.h / N.p := ⟨_, rfl⟩
  have hrr0 : 0 < rr := by rw [hrr]; positivity
  have hrr1 : rr ≤ 1 := by rw [hrr, div_le_one hpp]; exact hp
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = N.h * w / G := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; positivity
  have hη : N.h / N.H i ≤ e := by
    rw [he, div_le_div_iff₀ hHp hm0]; linarith
  have hve : v ≤ rr + e := by
    have h1 : N.p * N.H i * w ≤ N.H i * G + N.p * G := by nlinarith [hpHw, hFS]
    have h2 : v ≤ rr + N.h / N.H i := by
      rw [hv, hrr, div_add_div _ _ hpp.ne' hHp.ne', div_le_div_iff₀ hG0 (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h1 hh.le]
    linarith
  -- the savings cap, pointwise
  have hsav : ∀ x ∈ Set.Ico 0 w, (G - N.F i (Sh - x)) / G ≤ gb e rr v (x / w) := by
    intro x hx
    obtain ⟨hx0, hxw⟩ := hx
    have hFx0 := hF0 (Sh - x)
    have hs1 : G - N.F i (Sh - x) ≤ N.p * (w - x) := by
      have := hFslope sh (Sh - x) (by rw [hw] at hxw; linarith)
      rw [hFs] at this
      rw [hw]; linarith
    have hs2 : G - N.F i (Sh - x) ≤ G + N.H i * G / N.p - N.H i * (w - x) := by
      have h1 := hslopeH x hx0
      have h2 : N.H i * w - N.H i * G / N.p ≤ N.F i Sh := by
        have : N.H i * G / N.p = N.H i * G * (1 / N.p) := by ring
        rw [this]
        have h3 : N.p * N.H i * w - N.H i * G ≤ N.p * N.F i Sh := by linarith
        have h4 : (N.p * N.H i * w - N.H i * G) / N.p ≤ N.F i Sh := by
          rw [div_le_iff₀ hpp]; linarith
        have h5 : (N.p * N.H i * w - N.H i * G) / N.p = N.H i * w - N.H i * G * (1 / N.p) := by
          field_simp
        linarith
      linarith
    unfold gb
    refine le_min ?_ (le_min ?_ ?_)
    · rw [div_le_one hG0]; linarith
    · have : v * (1 - x / w) / rr = N.p * (w - x) / G := by
        rw [hv, hrr]; field_simp
      rw [this]
      exact div_le_div_of_nonneg_right hs1 hG0.le
    · rcases le_or_gt 0 (rr - v + v * (x / w)) with hc | hc
      · have h1 : 1 ≤ (e + rr - v + v * (x / w)) / e := by rw [le_div_iff₀ he0]; linarith
        refine le_trans ?_ h1
        rw [div_le_one hG0]; linarith
      · have hηpos : 0 < N.h / N.H i := by positivity
        have hfrac : (G - N.F i (Sh - x)) / G
            ≤ 1 + (rr - v + v * (x / w)) / (N.h / N.H i) := by
          have : 1 + (rr - v + v * (x / w)) / (N.h / N.H i)
              = (G + N.H i * G / N.p - N.H i * (w - x)) / G := by
            rw [hrr, hv]; field_simp; ring
          rw [this]
          exact div_le_div_of_nonneg_right hs2 hG0.le
        have hmono : (rr - v + v * (x / w)) / (N.h / N.H i) ≤ (rr - v + v * (x / w)) / e := by
          rw [div_le_div_iff₀ hηpos he0]
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.2 hη)]
        calc (G - N.F i (Sh - x)) / G ≤ 1 + (rr - v + v * (x / w)) / (N.h / N.H i) := hfrac
          _ ≤ 1 + (rr - v + v * (x / w)) / e := by linarith [hmono]
          _ = (e + rr - v + v * (x / w)) / e := by field_simp; ring
  -- integrals over the window `[0, ŵ)`
  have hUreal : U.real (Set.Ico 0 w) = M := by rw [hM]; rfl
  have hInt : ∀ (f : ℝ → ℝ) (B : ℝ), Measurable f → (∀ x ∈ Set.Ico (0 : ℝ) w, ‖f x‖ ≤ B) →
      IntegrableOn f (Set.Ico 0 w) U := fun f B hf hb =>
    Measure.integrableOn_of_bounded hUe_top hf.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall hb))
  have hpsic : Continuous psi := by unfold psi; fun_prop
  have hgbc : Continuous (fun z => gb e rr v z) := by unfold gb; fun_prop
  have hz01 : ∀ x ∈ Set.Ico (0 : ℝ) w, 0 ≤ x / w ∧ x / w ≤ 1 := fun x hx =>
    ⟨div_nonneg hx.1 hw0.le, (div_le_one hw0).2 hx.2.le⟩
  have hve' : v ≤ e + rr := by linarith
  have iX : IntegrableOn (fun x : ℝ => x) (Set.Ico 0 w) U :=
    hInt _ w measurable_id fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2.le
  have iψ : IntegrableOn (fun x : ℝ => psi (x / w)) (Set.Ico 0 w) U :=
    hInt _ (3 / 8) (hpsic.measurable.comp (measurable_id.div_const w)) fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg _)]
      exact psi_le _ (hz01 x hx).1
  have iG : IntegrableOn (fun x : ℝ => gb e rr v (x / w)) (Set.Ico 0 w) U :=
    hInt _ 1 (hgbc.measurable.comp (measurable_id.div_const w)) fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gb_nonneg e rr v _ he0 hrr0 hv0.le hve'
        (hz01 x hx).1 (hz01 x hx).2)]
      exact gb_le_one _ _ _ _
  have iF : IntegrableOn (fun x : ℝ => N.F i (Sh - x)) (Set.Ico 0 w) U :=
    hInt _ G (hFc.measurable.comp (measurable_const.sub measurable_id)) fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
      exact hFI _ ⟨by rw [hw] at hx; linarith [hx.2], by linarith [hx.1]⟩
  have iC : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Set.Ico 0 w) U := fun c =>
    hInt _ |c| measurable_const fun x _ => le_of_eq (Real.norm_eq_abs c)
  -- mean depletion
  have hIX : ∫ x in Set.Ico 0 w, x ∂U ≤ w / 2 * M := by
    have h1 := renewal_depletion_mean ρi w hw0.le
    rw [← hU] at h1
    have h2 : ∫ x in Set.Ico 0 w, x ∂U
        = (∫⁻ x in Set.Ico 0 w, ENNReal.ofReal x ∂U).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        ((ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall fun x hx => hx.1))
        measurable_id.aestronglyMeasurable
    rw [h2, hM]
    calc (∫⁻ x in Set.Ico 0 w, ENNReal.ofReal x ∂U).toReal
        ≤ (ENNReal.ofReal (w / 2) * U (Set.Ico 0 w)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUe_top) h1
      _ = w / 2 * (U (Set.Ico 0 w)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  -- setup cost through the savings
  have hk_le : k ≤ G * ∫ x in Set.Ico 0 w, gb e rr v (x / w) ∂U := by
    have h1 : ∫ x in Set.Ico 0 w, (G - N.F i (Sh - x)) ∂U = G * M - IF := by
      rw [integral_sub (iC G) iF, setIntegral_const, hUreal, smul_eq_mul, mul_comm]
    have h2 : G * M = k + IF := by rw [hGv]; field_simp
    have h3 : ∫ x in Set.Ico 0 w, (G - N.F i (Sh - x)) ∂U
        ≤ ∫ x in Set.Ico 0 w, G * gb e rr v (x / w) ∂U :=
      setIntegral_mono_on (Integrable.sub (iC G) iF) (Integrable.const_mul iG G) measurableSet_Ico
        fun x hx => by
          have := hsav x hx
          rw [div_le_iff₀ hG0] at this
          linarith
    rw [integral_const_mul] at h3
    linarith
  set IX := ∫ x in Set.Ico 0 w, x ∂U with hIXdef
  set Iψ := ∫ x in Set.Ico 0 w, psi (x / w) ∂U with hIψdef
  set Ig := ∫ x in Set.Ico 0 w, gb e rr v (x / w) ∂U with hIgdef
  have hIX0 : 0 ≤ IX := setIntegral_nonneg measurableSet_Ico fun x hx => hx.1
  have hIψ0 : 0 ≤ Iψ := setIntegral_nonneg measurableSet_Ico fun x _ => psi_nonneg _
  have hIg0 : 0 ≤ Ig := setIntegral_nonneg measurableSet_Ico fun x hx =>
    gb_nonneg e rr v _ he0 hrr0 hv0.le hve' (hz01 x hx).1 (hz01 x hx).2
  have hIg1 : Ig ≤ M := by
    have := setIntegral_mono_on iG (iC 1) measurableSet_Ico fun x _ => gb_le_one e rr v (x / w)
    rwa [setIntegral_const, hUreal, smul_eq_mul, mul_one] at this
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = N.h / (N.h + N.p) := ⟨_, rfl⟩
  have hα' : α = rr / (1 + rr) := by rw [hα, hrr]; field_simp; ring
  have hα0 : 0 < α := by rw [hα]; positivity
  have hEz : IX / (w * M) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith [hIX]
  have hEz0 : 0 ≤ IX / (w * M) := by positivity
  have hEg1 : Ig / M ≤ 1 := by rw [div_le_one hM0]; exact hIg1
  have hEg0 : 0 ≤ Ig / M := by positivity
  have hmin1 : min (3 / 8) (Iψ / M / α) ≤ 3 / 8 := min_le_left _ _
  have hmain : v * (IX / (w * M) + min (3 / 8) (Iψ / M / α)) + 7 * e / 12 * (Ig / M)
      ≤ 7 * (1 + e) / 8 := by
    have hW : v * (IX / (w * M) + min (3 / 8) (Iψ / M / α)) ≤ v * (7 / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hv0.le
    have hEgt : 7 * e / 12 * (Ig / M) ≤ 7 * e / 12 :=
      mul_le_of_le_one_right (by positivity) hEg1
    by_cases hca : rr ≤ 1 - 2 * e / 3
    · linarith only [hW, hEgt, hve', hca]
    by_cases hcb : v ≤ rr
    · linarith only [hW, hEgt, hcb, hrr1, he0]
    rw [not_le] at hca hcb
    have hcore : ∀ x ∈ Set.Ico (0 : ℝ) w,
        v * (3 * (x / w) / 4 + 2 * psi (x / w)) + 7 * e / 12 * gb e rr v (x / w) + v / 8
          + 3 * v * (1 - rr) / (8 * (1 + rr)) ≤ 7 * (1 + e) / 8 := fun x hx =>
      core e rr v (x / w) he0 he1 hrr1 hca hcb hve' (hz01 x hx).1 (hz01 x hx).2
    have e_int : (fun x : ℝ => v * (3 * (x / w) / 4 + 2 * psi (x / w))
        + 7 * e / 12 * gb e rr v (x / w) + v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr)))
        = fun x => 3 * v / (4 * w) * x + (2 * v * psi (x / w)
          + (7 * e / 12 * gb e rr v (x / w) + (v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr))))) := by
      funext x; ring
    have j1 : IntegrableOn (fun x : ℝ => 3 * v / (4 * w) * x) (Set.Ico 0 w) U :=
      Integrable.const_mul iX _
    have j2 : IntegrableOn (fun x : ℝ => 2 * v * psi (x / w)) (Set.Ico 0 w) U :=
      Integrable.const_mul iψ _
    have j3 : IntegrableOn (fun x : ℝ => 7 * e / 12 * gb e rr v (x / w)) (Set.Ico 0 w) U :=
      Integrable.const_mul iG _
    have j4 : IntegrableOn (fun _ : ℝ => v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr)))
        (Set.Ico 0 w) U := iC _
    have j34 : IntegrableOn (fun x : ℝ => 7 * e / 12 * gb e rr v (x / w)
        + (v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr)))) (Set.Ico 0 w) U := Integrable.add j3 j4
    have j234 : IntegrableOn (fun x : ℝ => 2 * v * psi (x / w) + (7 * e / 12 * gb e rr v (x / w)
        + (v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr))))) (Set.Ico 0 w) U := Integrable.add j2 j34
    have j1234 : IntegrableOn (fun x : ℝ => 3 * v / (4 * w) * x + (2 * v * psi (x / w)
        + (7 * e / 12 * gb e rr v (x / w) + (v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr))))))
        (Set.Ico 0 w) U := Integrable.add j1 j234
    have hint := setIntegral_mono_on (μ := U)
      (f := fun x : ℝ => v * (3 * (x / w) / 4 + 2 * psi (x / w))
        + 7 * e / 12 * gb e rr v (x / w) + v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr)))
      (by rw [e_int]; exact j1234)
      (iC (7 * (1 + e) / 8)) measurableSet_Ico hcore
    rw [e_int, setIntegral_const, hUreal, smul_eq_mul, integral_add j1 j234, integral_add j2 j34,
      integral_add j3 j4, integral_const_mul, integral_const_mul, integral_const_mul,
      setIntegral_const, hUreal, smul_eq_mul, ← hIXdef, ← hIψdef, ← hIgdef] at hint
    -- normalize by `M`
    have hdiv : v * (3 / 4 * (IX / (w * M)) + 2 * (Iψ / M)) + 7 * e / 12 * (Ig / M)
        + (v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr))) ≤ 7 * (1 + e) / 8 := by
      have e2 : v * (3 / 4 * (IX / (w * M)) + 2 * (Iψ / M)) + 7 * e / 12 * (Ig / M)
          + (v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr)))
          = (3 * v / (4 * w) * IX + (2 * v * Iψ + (7 * e / 12 * Ig
            + M * (v / 8 + 3 * v * (1 - rr) / (8 * (1 + rr)))))) / M := by
        field_simp; ring
      rw [e2, div_le_iff₀ hM0]
      linarith [hint]
    -- blend the two width bounds
    have hblend : min (3 / 8) (Iψ / M / α) ≤ 2 * (Iψ / M) + 3 * (1 - rr) / (8 * (1 + rr)) := by
      have hl0 : 0 ≤ 2 * rr / (1 + rr) := by positivity
      have hl1 : 2 * rr / (1 + rr) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hlam : 2 * rr / (1 + rr) * (Iψ / M / α) = 2 * (Iψ / M) := by
        rw [hα']; field_simp
      have e2 : (1 - 2 * rr / (1 + rr)) * (3 / 8) = 3 * (1 - rr) / (8 * (1 + rr)) := by
        field_simp; ring
      have h1 := mul_le_mul_of_nonneg_left (min_le_right (3 / 8) (Iψ / M / α)) hl0
      have h2 := mul_le_mul_of_nonneg_left (min_le_left (3 / 8) (Iψ / M / α)) (sub_nonneg.2 hl1)
      linarith
    have hb2 := mul_le_mul_of_nonneg_left hblend hv0.le
    have hEz2 : v * (IX / (w * M)) ≤ v * (1 / 2) := mul_le_mul_of_nonneg_left hEz hv0.le
    ring_nf at hb2 hEz2 hdiv ⊢
    linarith
  -- back to the original form
  have hIψ' : (∫ x in Set.Ico 0 w, max (1 - 4 * (x / w) / 3) 0 ^ 2 / (8 / 3) ∂U) = Iψ := rfl
  rw [hIψ']
  have hGv' : G * v = N.h * w := by rw [hv]; field_simp
  have e1 : N.h * IX / M = G * v * (IX / (w * M)) := by rw [hGv']; field_simp
  have e2 : N.h * (3 / 8) * w = G * v * (3 / 8) := by rw [hGv']; ring
  have e3 : (N.h + N.p) * w * Iψ / M = G * v * (Iψ / M / α) := by
    rw [hGv', hα]; field_simp
  rw [e1, e2, e3, ← mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ G * v)]
  have hkM : k / M ≤ G * (Ig / M) := by
    rw [div_le_iff₀ hM0]
    have e4 : G * (Ig / M) * M = G * Ig := by field_simp
    rw [e4]; exact hk_le
  have e5 : 7 / 8 * (1 + 1 / m) * G - 7 / (12 * m) * k / M
      = G * (7 * (1 + e) / 8) - 7 * e / 12 * (k / M) := by rw [he]; field_simp
  rw [e5]
  have h6 := mul_le_mul_of_nonneg_left hmain hG0.le
  have h7 : 7 * e / 12 * (k / M) ≤ 7 * e / 12 * (G * (Ig / M)) :=
    mul_le_mul_of_nonneg_left hkM (by positivity)
  ring_nf at h6 h7 ⊢
  linarith
