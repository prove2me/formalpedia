-- Prove2me | solution 1 for PuhaWardFluid.Limit.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T10:11:21.355826+00:00
-- url     : https://prove2.me/submissions/a76a68c9-6ef2-4fb8-ad7e-b4f08bfead8b

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit.L6aux

variable {H : ℝ≥0∞}

/-- The coercion `[0, H) → ℝ`. -/
noncomputable def coeR (z : Iv H) : ℝ := ((z : ℝ≥0) : ℝ)

lemma measurable_coeR : Measurable (coeR (H := H)) := by
  unfold coeR
  exact (NNReal.continuous_coe.comp continuous_subtype_val).measurable

/-- The pushforward of `μ` to `ℝ`. -/
noncomputable def nuR (μ : FiniteMeasure (Iv H)) : Measure ℝ :=
  (μ : Measure (Iv H)).map coeR

instance (μ : FiniteMeasure (Iv H)) : IsFiniteMeasure (nuR μ) := by
  unfold nuR; infer_instance

lemma Fcdf_eq (μ : FiniteMeasure (Iv H)) (x : ℝ) :
    Fcdf μ x = (nuR μ (Set.Iic x)).toReal := by
  unfold nuR
  rw [Measure.map_apply measurable_coeR measurableSet_Iic]
  rfl

lemma Fcdf_mono (μ : FiniteMeasure (Iv H)) : Monotone (Fcdf μ) := by
  intro a b hab
  rw [Fcdf_eq, Fcdf_eq]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hab))

lemma Fcdf_nonneg (μ : FiniteMeasure (Iv H)) (x : ℝ) : 0 ≤ Fcdf μ x := by
  rw [Fcdf_eq]; exact ENNReal.toReal_nonneg

lemma Fcdf_neg (μ : FiniteMeasure (Iv H)) (x : ℝ) (hx : x < 0) : Fcdf μ x = 0 := by
  unfold Fcdf
  have : {z : Iv H | ((z : ℝ≥0) : ℝ) ≤ x} = ∅ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx (z : ℝ≥0).2
  rw [this]; simp

lemma inv_le (μ : FiniteMeasure (Iv H)) {y a : ℝ} (ha : 0 ≤ a) (hy : y ≤ Fcdf μ a) :
    FcdfInv μ y ≤ ENNReal.ofReal a := by
  unfold FcdfInv
  refine iInf₂_le a.toNNReal ?_
  rwa [Real.coe_toNNReal _ ha]

lemma inv_ne_top (μ : FiniteMeasure (Iv H)) {y a : ℝ} (ha : 0 ≤ a) (hy : y ≤ Fcdf μ a) :
    FcdfInv μ y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (inv_le μ ha hy)

lemma inter_Iic (s : ℝ) : (⋂ n : ℕ, Set.Iic (s + 1 / ((n : ℝ) + 1))) = Set.Iic s := by
  ext a
  simp only [Set.mem_iInter, Set.mem_Iic]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    linarith [h n]
  · intro h n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- Right continuity of `F` at an infimum. -/
lemma le_Fcdf_inv (μ : FiniteMeasure (Iv H)) {y a : ℝ} (ha : 0 ≤ a) (hy : y ≤ Fcdf μ a) :
    y ≤ Fcdf μ (FcdfInv μ y).toReal := by
  set s := (FcdfInv μ y).toReal with hs
  have hfin := inv_ne_top μ ha hy
  have hseq : ∀ n : ℕ, y ≤ Fcdf μ (s + 1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : FcdfInv μ y < ENNReal.ofReal (s + 1 / ((n : ℝ) + 1)) := by
      rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      linarith
    unfold FcdfInv at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨x, hx⟩ := hlt
    rw [iInf_lt_iff] at hx
    obtain ⟨hxy, hxlt⟩ := hx
    have hx' : (x : ℝ) ≤ s + 1 / ((n : ℝ) + 1) := by
      have : (x : ℝ≥0∞) = ENNReal.ofReal (x : ℝ) := by simp
      rw [this, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hxlt
      exact hxlt.le
    exact hxy.trans (Fcdf_mono μ hx')
  have hT : Tendsto (fun n : ℕ => Fcdf μ (s + 1 / ((n : ℝ) + 1))) atTop (𝓝 (Fcdf μ s)) := by
    simp only [Fcdf_eq]
    have h1 := tendsto_measure_iInter_atTop (μ := nuR μ)
      (s := fun n : ℕ => Set.Iic (s + 1 / ((n : ℝ) + 1)))
      (fun n => measurableSet_Iic.nullMeasurableSet)
      (fun n m hnm => Set.Iic_subset_Iic.2 (by
        have := Nat.one_div_le_one_div (α := ℝ) hnm
        linarith)) ⟨0, measure_ne_top _ _⟩
    rw [inter_Iic] at h1
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  exact ge_of_tendsto' hT hseq

lemma FcdfInv_mono (μ : FiniteMeasure (Iv H)) : Monotone (FcdfInv μ) := by
  intro a b hab
  unfold FcdfInv
  exact iInf_mono fun x => iInf_mono' fun h => ⟨hab.trans h, le_rfl⟩

lemma measurable_q (μ : FiniteMeasure (Iv H)) :
    Measurable (fun y => (FcdfInv μ y).toReal) :=
  ENNReal.measurable_toReal.comp (FcdfInv_mono μ).measurable

lemma q_nonneg (μ : FiniteMeasure (Iv H)) (y : ℝ) : 0 ≤ (FcdfInv μ y).toReal :=
  ENNReal.toReal_nonneg

/-- The quantile transform: Lebesgue measure on `[0, F(x)]` pushed forward by `F^{-1}` is the
restriction of `μ` to `[0, x]`. -/
lemma map_q (μ : FiniteMeasure (Iv H)) (x : ℝ) (hx : 0 ≤ x) :
    (volume.restrict (Set.Icc 0 (Fcdf μ x))).map (fun y => (FcdfInv μ y).toReal) =
      (nuR μ).restrict (Set.Iic x) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) (Fcdf μ x))) := by
    constructor; rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply (measurable_q μ) measurableSet_Iic, Measure.restrict_apply
    ((measurable_q μ) measurableSet_Iic), Measure.restrict_apply measurableSet_Iic,
    Set.Iic_inter_Iic]
  set c := Fcdf μ (min a x) with hc
  have hc0 : 0 ≤ c := Fcdf_nonneg μ _
  have hνc : nuR μ (Set.Iic (min a x)) = ENNReal.ofReal c := by
    rw [hc, Fcdf_eq, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hνc]
  -- sandwich
  have hsub1 : Set.Ioc 0 c ⊆
      (fun y => (FcdfInv μ y).toReal) ⁻¹' Set.Iic a ∩ Set.Icc 0 (Fcdf μ x) := by
    intro y ⟨hy0, hyc⟩
    have ha : 0 ≤ a := by
      by_contra hneg
      push_neg at hneg
      have : c = 0 := by rw [hc]; exact Fcdf_neg μ _ (lt_of_le_of_lt (min_le_left _ _) hneg)
      linarith
    have hyx : y ≤ Fcdf μ x := hyc.trans (Fcdf_mono μ (min_le_right _ _))
    have hya : y ≤ Fcdf μ a := hyc.trans (Fcdf_mono μ (min_le_left _ _))
    refine ⟨?_, hy0.le, hyx⟩
    simp only [Set.mem_preimage, Set.mem_Iic]
    have := inv_le μ ha hya
    rw [← ENNReal.ofReal_toReal (inv_ne_top μ hx hyx), ENNReal.ofReal_le_ofReal_iff ha] at this
    exact this
  have hsub2 : (fun y => (FcdfInv μ y).toReal) ⁻¹' Set.Iic a ∩ Set.Icc 0 (Fcdf μ x) ⊆
      Set.Icc 0 c := by
    intro y ⟨hya, hy0, hyx⟩
    simp only [Set.mem_preimage, Set.mem_Iic] at hya
    refine ⟨hy0, ?_⟩
    have h1 := le_Fcdf_inv μ hx hyx
    have hle : (FcdfInv μ y).toReal ≤ min a x := by
      refine le_min hya ?_
      have := inv_le μ hx hyx
      rw [← ENNReal.ofReal_toReal (inv_ne_top μ hx hyx), ENNReal.ofReal_le_ofReal_iff hx] at this
      exact this
    exact h1.trans (Fcdf_mono μ hle)
  apply le_antisymm
  · calc _ ≤ volume (Set.Icc 0 c) := measure_mono hsub2
      _ = ENNReal.ofReal c := by simp
  · calc ENNReal.ofReal c = volume (Set.Ioc 0 c) := by simp
      _ ≤ _ := measure_mono hsub1

/-- General form of Lemma 6 for any finite measure on `[0, H)` and measurable `φ`. -/
lemma quantile_lintegral (μ : FiniteMeasure (Iv H)) (x : ℝ) (hx : 0 ≤ x) (φ : ℝ → ℝ≥0∞)
    (hφ : Measurable φ) :
    lpair ((Set.Iic x).indicator φ) μ =
      ∫⁻ y in Set.Icc (0 : ℝ) (Fcdf μ x), φ (FcdfInv μ y).toReal := by
  unfold lpair
  have h1 : ∫⁻ z, (Set.Iic x).indicator φ ((z : ℝ≥0) : ℝ) ∂(μ : Measure (Iv H)) =
      ∫⁻ r, (Set.Iic x).indicator φ r ∂(nuR μ) := by
    unfold nuR
    rw [lintegral_map (hφ.indicator measurableSet_Iic) measurable_coeR]
    rfl
  rw [h1, lintegral_indicator measurableSet_Iic, ← map_q μ x hx,
    lintegral_map hφ (measurable_q μ)]

end PuhaWardFluid.Limit.L6aux

open PuhaWardFluid.Limit PuhaWardFluid.Limit.L6aux

lemma PuhaWardFluid.Limit.L6aux.hazard_meas (g : ℝ → ℝ≥0) (hg : Measurable g) :
    Measurable (hazard g) := by
  unfold hazard
  have hI : Measurable (fun x : ℝ => ∫⁻ y in Set.Icc 0 x, (g y : ℝ≥0∞)) := by
    apply Monotone.measurable
    intro a b hab
    exact lintegral_mono_set (Set.Icc_subset_Icc le_rfl hab)
  have hcdf : Measurable (cdf g) := by
    unfold cdf
    exact ENNReal.measurable_toReal.comp hI
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_id) measurable_const)
  · exact (measurable_coe_nnreal_ennreal.comp hg).div
      (ENNReal.measurable_ofReal.comp (measurable_const.sub hcdf))

theorem solution {J : ℕ} (L : ClassLaws J) {Ω : Type*} (Q : QueueSeq J Ω) (N : ℕ+) (ω : Ω)
    (j : Fin J) (t : ℝ≥0) (x : ℝ) (hx0 : 0 ≤ x) (hxH : ENNReal.ofReal x < L.Hr j) :
    lpair ((Set.Iic x).indicator (L.hr j)) (Q.eta L N ω t j) =
      ∫⁻ y in Set.Icc (0 : ℝ) (Fcdf (Q.eta L N ω t j) x),
        hazardE (L.gr j) (FcdfInv (Q.eta L N ω t j) y) := by
  rw [quantile_lintegral _ x hx0 (L.hr j) (hazard_meas _ (L.gr_meas j))]
  refine setLIntegral_congr_fun measurableSet_Icc fun y hy => ?_
  unfold hazardE
  rw [if_neg (inv_ne_top _ hx0 hy.2)]
  rfl
