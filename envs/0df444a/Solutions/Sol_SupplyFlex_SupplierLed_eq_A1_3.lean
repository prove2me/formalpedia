-- Prove2me | solution 1 for SupplyFlex.SupplierLed.eq_A1_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:11:43.987957+00:00
-- url     : https://prove2.me/submissions/88382e04-e7ca-472f-960d-67213907c20b

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

open MeasureTheory SupplyFlex.SupplierLed

namespace EqA13Counter

/-- The ramp profile `1/4 + 5 (x − 1)⁺`. -/
noncomputable def gr (x : ℝ) : ℝ := 1 / 4 + 5 * max (x - 1) 0

/-- Demand density: `1/4` on `[0, 1)`, then rising linearly to the end `3/2` of the support. -/
noncomputable def rf : ℝ → ℝ := Set.indicator (Set.Ico 0 (3 / 2)) gr

noncomputable def RM : Model := ⟨1, 3 / 860, 7 / 10, 25 / 86, rf, ENNReal.ofReal (3 / 2)⟩

lemma gr_cont : Continuous gr := by unfold gr; fun_prop

lemma gr_pos (x : ℝ) : 0 < gr x := by unfold gr; positivity

lemma gr_mono {a b : ℝ} (h : a ≤ b) : gr a ≤ gr b := by
  unfold gr; have := max_le_max_right 0 (show a - 1 ≤ b - 1 by linarith); linarith

lemma rf_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 3 / 2) : rf x = gr x := by
  unfold rf; rw [Set.indicator_of_mem (by exact ⟨h0, h1⟩)]

lemma rf_nonneg (x : ℝ) : 0 ≤ rf x := by
  unfold rf; exact Set.indicator_nonneg (fun y _ => (gr_pos y).le) x

lemma supp_iff (x : ℝ) : x ∈ supp (ENNReal.ofReal (3 / 2)) ↔ x ∈ Set.Ico (0:ℝ) (3 / 2) := by
  unfold supp
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).2 h1⟩

lemma rf_integrable : Integrable rf := by
  unfold rf
  exact (integrable_indicator_iff measurableSet_Ico).2
    ((gr_cont.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)

/-- `F̄(x) = ∫ₓ^{3/2} g` on `[0, 3/2]`. -/
lemma Fbar_rf (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 3 / 2) :
    Fbar rf x = ∫ t in x..(3 / 2), gr t := by
  unfold Fbar rf
  rw [setIntegral_indicator measurableSet_Ico]
  have : Set.Ioi x ∩ Set.Ico (0:ℝ) (3 / 2) = Set.Ioo x (3 / 2) := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ico, Set.mem_Ioo]
    constructor
    · rintro ⟨a, _, c⟩; exact ⟨a, c⟩
    · rintro ⟨a, c⟩; exact ⟨a, by linarith, c⟩
  rw [this, intervalIntegral.integral_of_le h1, integral_Ioc_eq_integral_Ioo]

/-- The integral of `g` over an interval of the ramp. -/
lemma int_ramp (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, gr t = (b - a) / 4 + 5 / 2 * ((b - 1) ^ 2 - (a - 1) ^ 2) := by
  have : ∫ t in a..b, gr t = ∫ t in a..b, (1 / 4 + 5 * (t - 1)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hab] at ht
    simp only [gr]; rw [max_eq_left (by linarith [ht.1])]
  rw [this, intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_id.sub intervalIntegrable_const).const_mul 5),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma int_flat (a b : ℝ) (hb : b ≤ 1) (hab : a ≤ b) :
    ∫ t in a..b, gr t = (b - a) / 4 := by
  have : ∫ t in a..b, gr t = ∫ t in a..b, (1 / 4 : ℝ) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hab] at ht
    simp only [gr]; rw [max_eq_right (by linarith [ht.2])]; ring
  rw [this, intervalIntegral.integral_const, smul_eq_mul]; ring

lemma Fbar_ramp (x : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ 3 / 2) :
    Fbar rf x = (3 / 2 - x) / 4 + 5 / 2 * ((1 / 2) ^ 2 - (x - 1) ^ 2) := by
  rw [Fbar_rf x (by linarith) h2, int_ramp x (3 / 2) h1 h2]; ring

lemma Fbar_flat (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Fbar rf x = 1 - x / 4 := by
  rw [Fbar_rf x h0 (by linarith), ← intervalIntegral.integral_add_adjacent_intervals
    (b := 1) (gr_cont.intervalIntegrable _ _) (gr_cont.intervalIntegrable _ _),
    int_flat x 1 le_rfl h1, int_ramp 1 (3 / 2) le_rfl (by norm_num)]
  ring

lemma Fbar_pos_rf (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 3 / 2) : 0 < Fbar rf x := by
  rw [Fbar_rf x h0 h1.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (gr_cont.intervalIntegrable _ _)
    (fun t _ => gr_pos t) h1

lemma Fbar_anti_rf {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 3 / 2) :
    Fbar rf b ≤ Fbar rf a := by
  rw [Fbar_rf a h0 (le_trans hab hb), Fbar_rf b (le_trans h0 hab) hb]
  have e := intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b) (c := 3 / 2)
    (μ := volume) (f := gr) (gr_cont.intervalIntegrable _ _) (gr_cont.intervalIntegrable _ _)
  have : 0 ≤ ∫ t in a..b, gr t :=
    intervalIntegral.integral_nonneg hab (fun t _ => (gr_pos t).le)
  linarith

lemma std : RM.Std where
  c_pos := by norm_num [RM]
  p_pos := by norm_num [RM]
  p_le_one := by norm_num [RM]
  assm1_s := by norm_num [RM]
  assm1_r := by norm_num [RM]
  abar_pos := by simp [RM]
  f_meas := by
    show Measurable rf
    exact gr_cont.measurable.indicator measurableSet_Ico
  f_pos := by
    intro x hx
    show 0 < rf x
    have hx' := (supp_iff x).1 hx
    rw [rf_of_mem hx'.1 hx'.2]; exact gr_pos x
  f_zero := by
    intro x hx
    show rf x = 0
    have hx' : x ∉ Set.Ico (0:ℝ) (3 / 2) := fun h => hx ((supp_iff x).2 h)
    unfold rf; exact Set.indicator_of_notMem hx' _
  f_int := by
    show Integrable rf ∧ ∫ x, rf x = 1
    refine ⟨rf_integrable, ?_⟩
    unfold rf
    rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num),
      ← intervalIntegral.integral_add_adjacent_intervals (b := 1)
        (gr_cont.intervalIntegrable _ _) (gr_cont.intervalIntegrable _ _),
      int_flat 0 1 le_rfl (by norm_num), int_ramp 1 (3 / 2) le_rfl (by norm_num)]
    norm_num
  mean_fin := by
    show Integrable (fun x => x * rf x)
    have : (fun x => x * rf x) = Set.indicator (Set.Ico (0:ℝ) (3 / 2)) (fun x => x * gr x) := by
      funext x
      by_cases hx : x ∈ Set.Ico (0:ℝ) (3 / 2)
      · rw [Set.indicator_of_mem hx, rf_of_mem hx.1 hx.2]
      · rw [Set.indicator_of_notMem hx]; unfold rf; rw [Set.indicator_of_notMem hx, mul_zero]
    rw [this]
    exact (integrable_indicator_iff measurableSet_Ico).2
      (((continuous_id.mul gr_cont).integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
  igfr := by
    show MonotoneOn (fun ξ => ξ * rf ξ / Fbar rf ξ) (supp (ENNReal.ofReal (3 / 2)))
    intro a ha b hb hab
    have ha' := (supp_iff a).1 ha
    have hb' := (supp_iff b).1 hb
    simp only
    rw [rf_of_mem ha'.1 ha'.2, rf_of_mem hb'.1 hb'.2]
    have hFa := Fbar_pos_rf a ha'.1 ha'.2
    have hFb := Fbar_pos_rf b hb'.1 hb'.2
    have hFab := Fbar_anti_rf ha'.1 hab hb'.2.le
    have hnum : a * gr a ≤ b * gr b :=
      mul_le_mul hab (gr_mono hab) (gr_pos a).le (le_trans ha'.1 hab)
    have hnum0 : 0 ≤ a * gr a := mul_nonneg ha'.1 (gr_pos a).le
    rw [div_le_div_iff₀ hFa hFb]
    nlinarith [mul_le_mul_of_nonneg_left hFab hnum0, mul_le_mul_of_nonneg_right hnum hFa.le]
  f_cont := by
    show ContinuousOn rf (supp (ENNReal.ofReal (3 / 2)))
    refine gr_cont.continuousOn.congr (fun x hx => ?_)
    have hx' := (supp_iff x).1 hx
    exact rf_of_mem hx'.1 hx'.2

end EqA13Counter

open EqA13Counter in
theorem solution : ¬ (∀ (M : Model) (hM : M.Std) (qt qo qh : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hsr : M.s ≤ M.r),
    wo M qo qh ≤ M.r * Fbar M.f qt) := by
  intro h
  have F1 : Fbar rf 1 = 3 / 4 := by rw [Fbar_ramp 1 le_rfl (by norm_num)]; norm_num
  have Fo : Fbar rf (27 / 25) = 357 / 500 := by
    rw [Fbar_ramp _ (by norm_num) (by norm_num)]; norm_num
  have Fh : Fbar rf (3 / 5) = 17 / 20 := by rw [Fbar_flat _ (by norm_num) (by norm_num)]; norm_num
  have f1 : rf 1 = 1 / 4 := by
    rw [rf_of_mem (by norm_num) (by norm_num)]; unfold gr; norm_num
  have fo : rf (27 / 25) = 13 / 20 := by
    rw [rf_of_mem (by norm_num) (by norm_num)]; unfold gr; norm_num
  have fh : rf (3 / 5) = 1 / 4 := by
    rw [rf_of_mem (by norm_num) (by norm_num)]; unfold gr; norm_num
  have key := h RM std 1 (27 / 25) (3 / 5)
    (fun _ => ⟨by norm_num, by simp only [RM, G]; rw [F1, f1]; norm_num⟩)
    ⟨by norm_num, by simp only [RM, G]; rw [Fo, fo]; norm_num⟩
    ⟨fun _ => ⟨by norm_num, by simp only [RM, G]; rw [Fh, fh]; norm_num⟩,
      fun h' => by simp only [RM] at h'; norm_num at h'⟩
    (by simp only [RM]; norm_num)
  simp only [RM, wo] at key
  rw [F1, Fo, Fh] at key
  norm_num at key
