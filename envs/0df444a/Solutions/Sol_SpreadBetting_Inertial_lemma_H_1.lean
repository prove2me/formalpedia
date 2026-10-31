-- Prove2me | solution 1 for SpreadBetting.Inertial.lemma_H_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:30:10.502623+00:00
-- url     : https://prove2.me/submissions/aa1b50d2-1a88-4fb4-a0de-13555757ba67

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain

open MeasureTheory ProbabilityTheory Filter Topology

namespace SBH1Aux
open SpreadBetting.Inertial

lemma feps_cont {M : Market} (hM : M.Standing) : Continuous M.feps :=
  hM.feps_contDiff.continuous

lemma Feps_sub {M : Market} (hM : M.Standing) (a b : ℝ) :
    Feps M b - Feps M a = ∫ t in a..b, M.feps t := by
  unfold Feps
  exact intervalIntegral.integral_Iic_sub_Iic hM.feps_integrable.integrableOn
    hM.feps_integrable.integrableOn

lemma Feps_zero {M : Market} (hM : M.Standing) : Feps M 0 = 1 / 2 := by
  have h1 := intervalIntegral.integral_Iic_add_Ioi (b := (0:ℝ)) (μ := volume)
    hM.feps_integrable.integrableOn hM.feps_integrable.integrableOn
  rw [hM.feps_integral] at h1
  have h2 : ∫ x in Set.Ioi (0:ℝ), M.feps x = ∫ x in Set.Iic (0:ℝ), M.feps x := by
    have : ∫ x in Set.Ioi (0:ℝ), M.feps x = ∫ x in Set.Ioi (0:ℝ), M.feps (-x) := by
      congr 1; ext x; exact hM.feps_symm x
    rw [this, integral_comp_neg_Ioi]
    simp
  unfold Feps
  linarith

lemma Feps_lt {M : Market} (hM : M.Standing) (a b : ℝ) (hab : a < b)
    (hpos : ∀ t ∈ Set.Ioo a b, 0 < M.feps t) : Feps M a < Feps M b := by
  have h := Feps_sub hM a b
  have : 0 < ∫ t in a..b, M.feps t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((feps_cont hM).intervalIntegrable a b) hpos hab
  linarith

/-- `α < F_1((m0+m1)/2) < 1/2`. -/
lemma key_ineqs {M : Market} (hM : M.Standing) :
    alpha M < F M 1 ((M.m0 + M.m1) / 2) ∧ F M 1 ((M.m0 + M.m1) / 2) < 1 / 2 := by
  have hm := hM.m0_lt_m1
  have hR : ∀ t ∈ Set.Ioo (M.m0 - M.m1) 0, 0 < M.feps t := by
    intro t ht
    apply hM.feps_pos
    rw [abs_le]
    have h1 := hM.sL_lt_m0
    have : M.m1 - M.sL ≤ max (M.sH - M.m0) (M.m1 - M.sL) := le_max_right _ _
    constructor <;> linarith [ht.1, ht.2]
  unfold alpha F med
  simp only [Fin.isValue, one_ne_zero, if_false]
  constructor
  · apply Feps_lt hM _ _ (by linarith)
    intro t ht; apply hR; constructor <;> linarith [ht.1, ht.2]
  · rw [← Feps_zero hM]
    apply Feps_lt hM _ _ (by linarith)
    intro t ht; apply hR; constructor <;> linarith [ht.1, ht.2]

lemma r0_pos {M : Market} (hM : M.Standing) : 0 < r0 M := by
  unfold r0
  have := (key_ineqs hM).2
  exact inv_pos.2 (by linarith)

lemma rbar_le_two (M : Market) : rbar M ≤ 2 := by
  unfold rbar
  split_ifs <;> exact min_le_left _ _

end SBH1Aux

open SpreadBetting.Inertial SBH1Aux in
theorem solution (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    SlowlyVanishing M (rhoIP M r) ∧ Regular (rhoIP M r) := by
  have hr0' := r0_pos hM
  have hr2 : r < 2 := lt_of_lt_of_le hr (rbar_le_two M)
  have hki := key_ineqs hM
  -- z / (r0 + r z) → 1/r
  have hlin : Tendsto (fun z : ℕ => r0 M + r * (z : ℝ)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    exact Tendsto.const_mul_atTop hr0 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun z : ℕ => (r0 M + r * (z : ℝ))⁻¹) atTop (𝓝 0) :=
    hlin.inv_tendsto_atTop
  have hpos : ∀ z : ℕ, 0 < r0 M + r * (z : ℝ) := fun z => by positivity
  have hzr : Tendsto (fun z : ℕ => (z : ℝ) * rhoIP M r z) atTop (𝓝 (1 / r)) := by
    have : Tendsto (fun z : ℕ => 1 / r - (r0 M / r) * (r0 M + r * (z : ℝ))⁻¹) atTop
        (𝓝 (1 / r - (r0 M / r) * 0)) := tendsto_const_nhds.sub (hinv.const_mul _)
    rw [mul_zero, sub_zero] at this
    refine this.congr (fun z => ?_)
    unfold rhoIP
    have := hpos z
    field_simp
    ring
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro z _
    unfold rhoIP
    have hp := hpos z
    refine ⟨by positivity, ?_⟩
    have hrz : (0:ℝ) ≤ r * z := by positivity
    have h1 : 1 / (r0 M + r * (z : ℝ)) ≤ 1 / r0 M :=
      one_div_le_one_div_of_le hr0' (by linarith)
    have h2 : 1 / r0 M = 1 / 2 - F M 1 ((M.m0 + M.m1) / 2) := by
      unfold r0; rw [one_div, inv_inv]
    linarith [hki.1]
  · have hE : Tendsto (fun z : ℕ => (((z : ℝ) * rhoIP M r z : ℝ) : EReal)) atTop
        (𝓝 ((1 / r : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hzr
    rw [hE.liminf_eq]
    have : (1 / 4 : ℝ) < 1 / r := by
      rw [lt_one_div (by norm_num) hr0]; linarith
    have h' : ((1 / 4 : ℝ) : EReal) < ((1 / r : ℝ) : EReal) := by exact_mod_cast this
    exact h'
  · have : Tendsto (fun z : ℕ => rhoIP M r z) atTop (𝓝 0) := by
      refine hinv.congr (fun z => ?_)
      unfold rhoIP; rw [one_div]
    exact this
  · refine ⟨((1 : ℝ) : EReal), ?_⟩
    apply (continuous_coe_real_ereal.tendsto _).comp
    have h1 : Tendsto (fun z : ℕ => r * ((z : ℝ) * rhoIP M r z)) atTop (𝓝 (r * (1 / r))) :=
      hzr.const_mul r
    rw [mul_one_div_cancel hr0.ne'] at h1
    refine h1.congr (fun z => ?_)
    unfold rhoIP
    have := hpos z
    have := hpos (z + 1)
    push_cast at this ⊢
    field_simp
    ring
