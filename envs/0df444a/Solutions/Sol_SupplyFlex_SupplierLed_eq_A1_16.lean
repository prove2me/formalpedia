-- Prove2me | solution 1 for SupplyFlex.SupplierLed.eq_A1_16
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-20T05:28:37.637522+00:00
-- url     : https://prove2.me/submissions/26ca2e85-84d3-4b61-99cc-4b06565a054d

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_LogConcaveOn
import Definitions.Def_SupplyFlex_SupplierLed_Setting

open MeasureTheory SupplyFlex.SupplierLed

namespace EqA116Counter

/-- Uniform density on `[0, 1)`. -/
noncomputable def uf : ℝ → ℝ := Set.indicator (Set.Ico 0 1) (fun _ => 1)

noncomputable def UM : Model := ⟨1, 1/10, 1/2, 1/2, uf, 1⟩

lemma uf_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : uf x = 1 := by
  unfold uf; rw [Set.indicator_of_mem (by exact ⟨h0, h1⟩)]

lemma uf_nonneg (x : ℝ) : 0 ≤ uf x := by
  unfold uf; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma supp_one (x : ℝ) : x ∈ supp 1 ↔ x ∈ Set.Ico (0:ℝ) 1 := by
  unfold supp
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  constructor
  · rintro ⟨h0, h1⟩; exact ⟨h0, (ENNReal.ofReal_lt_one).1 h1⟩
  · rintro ⟨h0, h1⟩; exact ⟨h0, (ENNReal.ofReal_lt_one).2 h1⟩

lemma Fbar_uf (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Fbar uf q = 1 - q := by
  unfold Fbar uf
  rw [setIntegral_indicator measurableSet_Ico, setIntegral_const]
  have : Set.Ioi q ∩ Set.Ico (0:ℝ) 1 = Set.Ioo q 1 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ico, Set.mem_Ioo]
    constructor
    · rintro ⟨a, _, c⟩; exact ⟨a, c⟩
    · rintro ⟨a, c⟩; exact ⟨a, by linarith, c⟩
  rw [this, Real.volume_real_Ioo_of_le h1, smul_eq_mul, mul_one]

lemma G_uf (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : G uf q = 1 - 2 * q := by
  unfold G; rw [Fbar_uf q h0 h1.le, uf_of_mem h0 h1]; ring

lemma T_uf (z K : ℝ) (h0 : 0 ≤ z) (h1 : z < 1) :
    ∫ x in Set.Ioc 0 z, (x * uf x + K) = z ^ 2 / 2 + K * z := by
  have : ∫ x in Set.Ioc 0 z, (x * uf x + K) = ∫ x in Set.Ioc 0 z, (x + K) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [uf_of_mem hx.1.le (lt_of_le_of_lt hx.2 h1), mul_one]
  rw [this, ← intervalIntegral.integral_of_le h0, intervalIntegral.integral_add
    intervalIntegral.intervalIntegrable_id intervalIntegrable_const, integral_id,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma T_uf' (z : ℝ) (h0 : 0 ≤ z) (h1 : z < 1) :
    ∫ x in Set.Ioc 0 z, x * uf x = z ^ 2 / 2 := by
  have := T_uf z 0 h0 h1
  simp only [add_zero, zero_mul] at this
  exact this

lemma std : UM.Std where
  c_pos := by norm_num [UM]
  p_pos := by norm_num [UM]
  p_le_one := by norm_num [UM]
  assm1_s := by norm_num [UM]
  assm1_r := by norm_num [UM]
  abar_pos := by simp [UM]
  f_meas := by
    show Measurable uf
    exact measurable_const.indicator measurableSet_Ico
  f_pos := by
    intro x hx
    show 0 < uf x
    have hx' := (supp_one x).1 hx
    rw [uf_of_mem hx'.1 hx'.2]; norm_num
  f_zero := by
    intro x hx
    show uf x = 0
    have hx' : x ∉ Set.Ico (0:ℝ) 1 := fun h => hx ((supp_one x).2 h)
    unfold uf; exact Set.indicator_of_notMem hx' _
  f_int := by
    show Integrable uf ∧ ∫ x, uf x = 1
    constructor
    · unfold uf
      exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by simp))
    · unfold uf
      rw [integral_indicator measurableSet_Ico, setIntegral_const,
        Real.volume_real_Ico_of_le zero_le_one]
      norm_num
  mean_fin := by
    show Integrable (fun x => x * uf x)
    have : (fun x => x * uf x) = Set.indicator (Set.Ico (0:ℝ) 1) (fun x => x) := by
      funext x
      by_cases hx : x ∈ Set.Ico (0:ℝ) 1
      · rw [Set.indicator_of_mem hx, uf_of_mem hx.1 hx.2, mul_one]
      · rw [Set.indicator_of_notMem hx]
        unfold uf; rw [Set.indicator_of_notMem hx, mul_zero]
    rw [this]
    exact (integrable_indicator_iff measurableSet_Ico).2
      ((continuous_id.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
  igfr := by
    show MonotoneOn (fun ξ => ξ * uf ξ / Fbar uf ξ) (supp 1)
    intro a ha b hb hab
    have ha' := (supp_one a).1 ha
    have hb' := (supp_one b).1 hb
    simp only
    rw [uf_of_mem ha'.1 ha'.2, uf_of_mem hb'.1 hb'.2, Fbar_uf a ha'.1 ha'.2.le,
      Fbar_uf b hb'.1 hb'.2.le, mul_one, mul_one]
    have h1 : 0 < 1 - a := by linarith [ha'.2]
    have h2 : 0 < 1 - b := by linarith [hb'.2]
    rw [div_le_div_iff₀ h1 h2]
    nlinarith
  f_cont := by
    show ContinuousOn uf (supp 1)
    refine (continuousOn_const (c := (1:ℝ))).congr (fun x hx => ?_)
    have hx' := (supp_one x).1 hx
    exact uf_of_mem hx'.1 hx'.2

lemma logconc : ConvexOptimization.LogConcaveOn Set.univ UM.f := by
  show ConvexOptimization.LogConcaveOn Set.univ uf
  refine ⟨fun x _ => uf_nonneg x, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  by_cases hx : x ∈ Set.Ico (0:ℝ) 1
  · by_cases hy : y ∈ Set.Ico (0:ℝ) 1
    · rw [uf_of_mem hx.1 hx.2, uf_of_mem hy.1 hy.2, Real.one_rpow, Real.one_rpow, one_mul]
      have hm : a * x + b * y ∈ Set.Ico (0:ℝ) 1 := by
        constructor
        · nlinarith [hx.1, hy.1]
        · rcases ha.lt_or_eq with ha' | ha'
          · nlinarith [hx.2, hy.2, hy.1, mul_pos ha' (sub_pos.2 hx.2), mul_nonneg hb (sub_nonneg.2 hy.2.le)]
          · subst ha'
            have : b = 1 := by linarith
            subst this; linarith [hy.2]
      rw [uf_of_mem hm.1 hm.2]
    · have hy0 : uf y = 0 := by unfold uf; exact Set.indicator_of_notMem hy _
      rw [hy0]
      rcases hb.lt_or_eq with hb' | hb'
      · rw [Real.zero_rpow hb'.ne', mul_zero]; exact uf_nonneg _
      · subst hb'
        have : a = 1 := by linarith
        subst this
        simp
  · have hx0 : uf x = 0 := by unfold uf; exact Set.indicator_of_notMem hx _
    rw [hx0]
    rcases ha.lt_or_eq with ha' | ha'
    · rw [Real.zero_rpow ha'.ne', zero_mul]; exact uf_nonneg _
    · subst ha'
      have : b = 1 := by linarith
      subst this
      simp

end EqA116Counter

open EqA116Counter in
theorem solution : ¬ (∀ (M : Model) (hM : M.Std) (hlc : ConvexOptimization.LogConcaveOn Set.univ M.f)
    (qt qo qh : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hsr : M.s ≤ M.r),
    ∫ x in Set.Ioc 0 qt, x * M.f x ≤
      M.p * ∫ x in Set.Ioc 0 qo, x * M.f x + (1 - M.p) * ∫ x in Set.Ioc 0 qh, x * M.f x) := by
  intro h
  have hG1 : G uf (13/40) = 1 - 2 * (13/40) := G_uf _ (by norm_num) (by norm_num)
  have hG2 : G uf (2/5) = 1 - 2 * (2/5) := G_uf _ (by norm_num) (by norm_num)
  have hG3 : G uf (1/4) = 1 - 2 * (1/4) := G_uf _ (by norm_num) (by norm_num)
  have key := h UM std logconc (13/40) (2/5) (1/4)
    (fun _ => ⟨by norm_num, by simp only [UM]; rw [hG1]; norm_num⟩)
    ⟨by norm_num, by simp only [UM]; rw [hG2]; norm_num⟩
    ⟨fun _ => ⟨by norm_num, by simp only [UM]; rw [hG3]; norm_num⟩,
      fun h => by simp only [UM] at h; norm_num at h⟩
    (by simp only [UM]; norm_num)
  simp only [UM] at key
  rw [T_uf' _ (by norm_num) (by norm_num), T_uf' (1/4) (by norm_num) (by norm_num),
    T_uf _ _ (by norm_num) (by norm_num)] at key
  norm_num at key
