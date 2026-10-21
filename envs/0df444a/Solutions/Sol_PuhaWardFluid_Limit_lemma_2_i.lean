-- Prove2me | solution 1 for PuhaWardFluid.Limit.lemma_2_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:00:51.70108+00:00
-- url     : https://prove2.me/submissions/d2df4d7e-b98b-480c-9dff-2085cae10e9c

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_FluidModel

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace PuhaWardFluid.Limit.L2iaux


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


lemma hazard_meas (g : ℝ → ℝ≥0) (hg : Measurable g) :
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


/-! ### P1. Continuity of primitives of (possibly non-measurable) nonnegative functions -/

lemma restrict_eq_of_le (φ g : ℝ → ℝ≥0∞) (hgle : g ≤ φ) (n : ℝ)
    (hfin : ∫⁻ u in Set.Icc (0 : ℝ) n, φ u < ⊤)
    (heq : ∫⁻ u in Set.Icc (0 : ℝ) n, φ u = ∫⁻ u in Set.Icc (0 : ℝ) n, g u)
    (t : ℝ) (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∫⁻ u in Set.Icc (0 : ℝ) t, g u = ∫⁻ u in Set.Icc (0 : ℝ) t, φ u := by
  have hsplit : Set.Icc (0 : ℝ) n = Set.Icc 0 t ∪ Set.Ioc t n := (Set.Icc_union_Ioc_eq_Icc ht0 htn).symm
  have hdisj : Disjoint (Set.Icc (0 : ℝ) t) (Set.Ioc t n) :=
    Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]
  have hrest : volume.restrict (Set.Icc (0 : ℝ) n) =
      volume.restrict (Set.Icc 0 t) + volume.restrict (Set.Ioc t n) := by
    rw [hsplit, Measure.restrict_union hdisj measurableSet_Ioc]
  have hφ := heq
  rw [hrest, lintegral_add_measure, lintegral_add_measure] at hφ
  have h1 : ∫⁻ u in Set.Icc (0 : ℝ) t, g u ≤ ∫⁻ u in Set.Icc (0 : ℝ) t, φ u := lintegral_mono hgle
  have h2 : ∫⁻ u in Set.Ioc t n, g u ≤ ∫⁻ u in Set.Ioc t n, φ u := lintegral_mono hgle
  have hfin2 : ∫⁻ u in Set.Ioc t n, φ u ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin.ne ?_
    rw [hrest, lintegral_add_measure]; exact le_add_self
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have := ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top hfin2 h2) hlt h2
  rw [← hφ] at this
  exact lt_irrefl _ this

lemma cont_lint (φ : ℝ → ℝ≥0∞) (hfin : ∀ t : ℝ≥0, ∫⁻ u in Set.Icc (0 : ℝ) t, φ u < ⊤) :
    Continuous (fun t : ℝ≥0 => (∫⁻ u in Set.Icc (0 : ℝ) t, φ u).toReal) := by
  rw [continuous_iff_continuousAt]
  intro t0
  set n : ℝ := (t0 : ℝ) + 1 with hn
  have hn0 : 0 ≤ n := by positivity
  have hfn : ∫⁻ u in Set.Icc (0 : ℝ) n, φ u < ⊤ := by
    exact hfin ⟨n, hn0⟩
  obtain ⟨g, hgm, hgle, hgeq⟩ := exists_measurable_le_lintegral_eq
    (μ := volume.restrict (Set.Icc (0 : ℝ) n)) φ
  have hgfin : ∫⁻ u in Set.Icc (0 : ℝ) n, g u ≠ ⊤ := by rw [← hgeq]; exact hfn.ne
  set ψ : ℝ → ℝ := fun u => (g u).toReal
  have hψint : IntegrableOn ψ (Set.uIcc 0 n) := by
    rw [Set.uIcc_of_le hn0]
    exact integrable_toReal_of_lintegral_ne_top hgm.aemeasurable hgfin
  have hcont := intervalIntegral.continuousOn_primitive_interval hψint
  rw [Set.uIcc_of_le hn0] at hcont
  have hG : ∀ t : ℝ≥0, (t : ℝ) ≤ n →
      (∫⁻ u in Set.Icc (0 : ℝ) t, φ u).toReal = ∫ u in (0 : ℝ)..t, ψ u := by
    intro t htn
    rw [← restrict_eq_of_le φ g hgle n hfn hgeq t t.2 htn,
      intervalIntegral.integral_of_le (NNReal.coe_nonneg t), ← integral_Icc_eq_integral_Ioc]
    have hgfin_t : ∫⁻ u in Set.Icc (0 : ℝ) t, g u ≠ ⊤ :=
      ne_top_of_le_ne_top hgfin (lintegral_mono_set (Set.Icc_subset_Icc le_rfl htn))
    rw [integral_toReal hgm.aemeasurable (ae_lt_top hgm hgfin_t)]
  have hnb : {t : ℝ≥0 | (t : ℝ) < n} ∈ 𝓝 t0 :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds (by simp [hn])
  have hcontAt : ContinuousAt (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..t, ψ u) t0 := by
    have h1 : ContinuousOn (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..t, ψ u) {t : ℝ≥0 | (t : ℝ) ≤ n} :=
      hcont.comp NNReal.continuous_coe.continuousOn (fun t ht => ⟨t.2, ht⟩)
    exact h1.continuousAt (Filter.mem_of_superset hnb fun t (ht : (t : ℝ) < n) =>
      show (t : ℝ) ≤ n from le_of_lt ht)
  refine hcontAt.congr ?_
  filter_upwards [hnb] with t ht
  exact (hG t ht.le).symm

/-! ### A. Distribution functions -/

section A
variable (g : ℝ → ℝ≥0) (hg : Measurable g) (hfin : ∫⁻ x, (g x : ℝ≥0∞) ≤ 1)
  (hneg : ∀ x, x < 0 → g x = 0)
include hfin

lemma cdf_props : Monotone (cdf g) ∧ ∀ r, 0 ≤ cdf g r ∧ cdf g r ≤ 1 := by
  have hle : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≤ 1 := fun r =>
    (setLIntegral_le_lintegral _ _).trans hfin
  have hfin' : ∀ r, ∫⁻ y in Set.Icc 0 r, (g y : ℝ≥0∞) ≠ ⊤ := fun r =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hle r)
  refine ⟨fun a b hab => ?_, fun r => ⟨ENNReal.toReal_nonneg, ?_⟩⟩
  · unfold cdf
    exact ENNReal.toReal_mono (hfin' b) (lintegral_mono_set (Set.Icc_subset_Icc le_rfl hab))
  · unfold cdf
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hle r)
    simpa using this

include hg in
lemma integrable_g : Integrable (fun y => (g y : ℝ)) := by
  refine ⟨(NNReal.continuous_coe.measurable.comp hg).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ y, ‖(g y : ℝ)‖ₑ = (g y : ℝ≥0∞) := fun y => by simp
  simp_rw [this]
  exact lt_of_le_of_lt hfin ENNReal.one_lt_top

include hg in
lemma cdf_eq_setIntegral (x : ℝ) : cdf g x = ∫ y in Set.Icc 0 x, (g y : ℝ) := by
  unfold cdf
  have h := integral_toReal (μ := volume.restrict (Set.Icc 0 x)) (f := fun y => (g y : ℝ≥0∞))
    ((measurable_coe_nnreal_ennreal.comp hg).aemeasurable)
    (Eventually.of_forall fun _ => ENNReal.coe_lt_top)
  simp only [ENNReal.coe_toReal] at h
  exact h.symm

include hg hneg in
lemma cdf_eq_primitive (x : ℝ) : cdf g x = ∫ y in (0 : ℝ)..x, (g y : ℝ) := by
  rw [cdf_eq_setIntegral g hg hfin]
  rcases le_or_gt 0 x with hx | hx
  · rw [intervalIntegral.integral_of_le hx, integral_Icc_eq_integral_Ioc]
  · rw [Set.Icc_eq_empty (not_le.2 hx), intervalIntegral.integral_symm,
      intervalIntegral.integral_of_le hx.le, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        (fun y hy => by simp [hneg y hy.2])]
    simp

include hg hneg in
lemma cdf_cont : Continuous (cdf g) := by
  have : cdf g = fun x => ∫ y in (0 : ℝ)..x, (g y : ℝ) := funext (cdf_eq_primitive g hg hfin hneg)
  rw [this]
  exact intervalIntegral.continuous_primitive
    (fun a b => (integrable_g g hg hfin).intervalIntegrable) 0

lemma cdf_zero : cdf g 0 = 0 := by
  unfold cdf
  rw [Set.Icc_self, Measure.restrict_singleton]
  simp

include hg hneg in
lemma edge_pos : 0 < edge g := by
  have hc := (cdf_cont g hg hfin hneg).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc (1 / 2) (by norm_num)
  have h1 : cdf g (δ / 2) < 1 := by
    have := h (x := δ / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
    rw [cdf_zero g hfin, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self (cdf g (δ / 2))]
  unfold edge
  refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun (x : ℝ) (_ : 0 ≤ x ∧ cdf g x < 1) =>
    ENNReal.ofReal x) (δ / 2) ⟨by linarith, h1⟩)
  simp; linarith

end A

/-! ### P2. Finiteness of the reneging integral -/

section P2
variable {H : ℝ≥0∞}

lemma Fcdf_tendsto_mass (μ : FiniteMeasure (Iv H)) :
    Tendsto (fun n : ℕ => Fcdf μ n) atTop (𝓝 (mass1 μ)) := by
  simp only [Fcdf_eq]
  have h1 := tendsto_measure_iUnion_atTop (μ := nuR μ) (s := fun n : ℕ => Set.Iic (n : ℝ))
    (fun a b hab => Set.Iic_subset_Iic.2 (by exact_mod_cast hab))
  have hU : (⋃ n : ℕ, Set.Iic (n : ℝ)) = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge x; exact ⟨n, hn⟩
  rw [hU] at h1
  have h2 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  have hm : (nuR μ Set.univ).toReal = mass1 μ := by
    unfold nuR mass1
    rw [Measure.map_apply measurable_coeR MeasurableSet.univ, Set.preimage_univ]
    rfl
  rw [hm] at h2
  exact h2

lemma inner_le (μ : FiniteMeasure (Iv H)) (g : ℝ → ℝ≥0) (hg : Measurable g) (Qv : ℝ)
    (hQ : Qv ≤ mass1 μ) :
    ∫⁻ z in Set.Icc 0 Qv, hazardE g (FcdfInv μ z) ≤ lpair (hazard g) μ := by
  have hn : ∀ n : ℕ, ∫⁻ z in Set.Icc 0 (Fcdf μ n), hazardE g (FcdfInv μ z) ≤
      lpair (hazard g) μ := by
    intro n
    have e := quantile_lintegral μ n (Nat.cast_nonneg n) (hazard g) (hazard_meas g hg)
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun y => hazard g (FcdfInv μ y).toReal)
      (fun y hy => by
        unfold hazardE
        rw [if_neg (inv_ne_top _ (Nat.cast_nonneg n) hy.2)]), ← e]
    unfold lpair
    exact lintegral_mono fun x => Set.indicator_le_self _ _ _
  have hsub : Set.Icc 0 Qv ⊆ (⋃ n : ℕ, Set.Icc 0 (Fcdf μ n)) ∪ {mass1 μ} := by
    intro z hz
    by_cases hzm : z < mass1 μ
    · left
      obtain ⟨n, hn⟩ := ((Fcdf_tendsto_mass μ).eventually (Ioi_mem_nhds hzm)).exists
      exact Set.mem_iUnion.2 ⟨n, hz.1, le_of_lt hn⟩
    · right
      exact le_antisymm (hz.2.trans hQ) (not_lt.1 hzm)
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Icc (0 : ℝ) (Fcdf μ n)) := by
    refine Monotone.directed_le fun a b hab => Set.Icc_subset_Icc le_rfl ?_
    exact Fcdf_mono μ (by exact_mod_cast hab)
  calc ∫⁻ z in Set.Icc 0 Qv, hazardE g (FcdfInv μ z)
      ≤ ∫⁻ z in (⋃ n : ℕ, Set.Icc 0 (Fcdf μ n)) ∪ {mass1 μ}, hazardE g (FcdfInv μ z) :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ z in (⋃ n : ℕ, Set.Icc 0 (Fcdf μ n)), hazardE g (FcdfInv μ z)) +
          ∫⁻ z in ({mass1 μ} : Set ℝ), hazardE g (FcdfInv μ z) := lintegral_union_le _ _ _
    _ = ⨆ n : ℕ, ∫⁻ z in Set.Icc 0 (Fcdf μ n), hazardE g (FcdfInv μ z) := by
        rw [setLIntegral_iUnion_of_directed _ hdir,
          setLIntegral_measure_zero _ _ Real.volume_singleton, add_zero]
    _ ≤ lpair (hazard g) μ := iSup_le hn

end P2


/-! ### P3. Weak continuity of measure-valued paths -/

section P3
variable {H : ℝ≥0∞}

lemma exists_seq (hH : 0 < H) : ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧ StrictMono a ∧
    (∀ k, ENNReal.ofReal (a k) < H) ∧ ∀ z : ℝ, ENNReal.ofReal z < H → ∃ k, z ≤ a k := by
  by_cases htop : H = ⊤
  · refine ⟨fun k => k, fun k => Nat.cast_nonneg k, fun a b h => show (a : ℝ) < b by exact_mod_cast h,
      fun k => by rw [htop]; exact ENNReal.ofReal_lt_top, fun z _ => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_ge z
    exact ⟨n, hn⟩
  · set h := H.toReal with hh
    have hpos : 0 < h := ENNReal.toReal_pos hH.ne' htop
    have hfrac : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 2) ∧ 1 / ((k : ℝ) + 2) < 1 := fun k => by
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    refine ⟨fun k => h * (1 - 1 / ((k : ℝ) + 2)), fun k => ?_, fun a b hab => ?_,
      fun k => ?_, fun z hz => ?_⟩
    · have := hfrac k
      exact mul_nonneg hpos.le (by linarith)
    · have hab' : (a : ℝ) < b := by exact_mod_cast hab
      have : 1 / ((b : ℝ) + 2) < 1 / ((a : ℝ) + 2) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      show h * (1 - 1 / ((a : ℝ) + 2)) < h * (1 - 1 / ((b : ℝ) + 2))
      exact mul_lt_mul_of_pos_left (by linarith) hpos
    · rw [← ENNReal.ofReal_toReal htop]
      refine (ENNReal.ofReal_lt_ofReal_iff hpos).2 ?_
      have := hfrac k
      show h * (1 - 1 / ((k : ℝ) + 2)) < h
      nlinarith
    · rcases lt_or_ge z 0 with hz0 | hz0
      · refine ⟨0, ?_⟩
        have := hfrac 0
        show z ≤ h * (1 - 1 / (((0 : ℕ) : ℝ) + 2))
        nlinarith
      have hzh : z < h := by
        rw [← ENNReal.ofReal_toReal htop] at hz
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hz0).1 hz
      have hq : 0 < 1 - z / h := by
        rw [sub_pos, div_lt_one hpos]; exact hzh
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hq
      refine ⟨n, ?_⟩
      have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : z / h < 1 - 1 / ((n : ℝ) + 2) := by linarith
      rw [div_lt_iff₀ hpos] at h2
      show z ≤ h * (1 - 1 / ((n : ℝ) + 2))
      linarith

lemma chiv_bounds (a b : ℝ) (x : ℝ≥0) :
    0 ≤ max 0 (min 1 ((b - x) / (b - a))) ∧ max 0 (min 1 ((b - x) / (b - a))) ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The cutoff `x ↦ clamp((b − x)/(b − a), 0, 1)`: `1` on `[0, a]`, `0` on `[b, ∞)`. -/
noncomputable def chi (a b : ℝ) : ℝ≥0 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max 0 (min 1 ((b - x) / (b - a))), by fun_prop⟩ 1 (by
      intro x y
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      have hx := chiv_bounds a b x
      have hy := chiv_bounds a b y
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])

lemma chi_apply (a b : ℝ) (x : ℝ≥0) : chi a b x = max 0 (min 1 ((b - x) / (b - a))) := rfl

lemma chi_one (a b : ℝ) (hab : a < b) (x : ℝ≥0) (hx : (x : ℝ) ≤ a) : chi a b x = 1 := by
  rw [chi_apply, min_eq_left]
  · simp
  · rw [le_div_iff₀ (by linarith)]; linarith

lemma chi_zero (a b : ℝ) (hab : a < b) (x : ℝ≥0) (hx : b ≤ (x : ℝ)) : chi a b x = 0 := by
  rw [chi_apply]
  apply max_eq_left
  refine (min_le_right _ _).trans ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- The retraction `x ↦ min x b` of `ℝ≥0` into `[0, H)`. -/
noncomputable def retr (b : ℝ) (hb : ENNReal.ofReal b < H) : C(ℝ≥0, Iv H) :=
  ⟨fun x => ⟨min x b.toNNReal, lt_of_le_of_lt (show ((min x b.toNNReal : ℝ≥0) : ℝ≥0∞) ≤
      (b.toNNReal : ℝ≥0∞) by exact_mod_cast min_le_right x b.toNNReal) hb⟩,
    (continuous_id.min continuous_const).subtype_mk _⟩

/-- The extension by the cutoff of a bounded continuous function on `[0, H)`. -/
noncomputable def gext (f : Iv H →ᵇ ℝ) (a b : ℝ) (hb : ENNReal.ofReal b < H) : ℝ≥0 →ᵇ ℝ :=
  chi a b * f.compContinuous (retr b hb)

lemma gext_apply (f : Iv H →ᵇ ℝ) (a b : ℝ) (hab : a < b) (hb0 : 0 ≤ b)
    (hb : ENNReal.ofReal b < H) (z : Iv H) :
    gext f a b hb (z : ℝ≥0) = chi a b z * f z := by
  unfold gext
  rw [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.compContinuous_apply]
  by_cases hz : (z : ℝ≥0) ≤ b.toNNReal
  · congr 2
    apply Subtype.ext
    show min (z : ℝ≥0) b.toNNReal = z
    exact min_eq_left hz
  · rw [chi_zero a b hab _ (by
      have : b.toNNReal < (z : ℝ≥0) := lt_of_not_ge hz
      have := (Real.toNNReal_lt_iff_lt_coe hb0).1 this
      exact this.le)]
    simp

lemma weak_cont (hH : 0 < H) (ν : ℝ≥0 → FiniteMeasure (Iv H))
    (hint : ∀ g : ℝ≥0 →ᵇ ℝ, Continuous (fun s => pair (fun x => g x.toNNReal) (ν s))) :
    Continuous ν := by
  have hint' : ∀ g : ℝ≥0 →ᵇ ℝ,
      Continuous (fun s => ∫ z, g (z : ℝ≥0) ∂(ν s : Measure (Iv H))) := by
    intro g
    have := hint g
    unfold pair at this
    simpa only [Real.toNNReal_coe] using this
  obtain ⟨a, ha0, hamono, haH, hacof⟩ := exists_seq hH
  rw [continuous_iff_continuousAt]
  intro t
  unfold ContinuousAt
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M := ‖f‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  set c : ℕ → ℝ≥0 →ᵇ ℝ := fun k => 1 - chi (a k) (a (k + 1)) with hc
  have hc_apply : ∀ k (x : ℝ≥0), c k x = 1 - chi (a k) (a (k + 1)) x := fun k x => by
    simp [hc]
  have hc01 : ∀ k (x : ℝ≥0), 0 ≤ c k x ∧ c k x ≤ 1 := fun k x => by
    rw [hc_apply]
    have := chiv_bounds (a k) (a (k + 1)) x
    rw [← chi_apply] at this
    constructor <;> linarith [this.1, this.2]
  have hval : Continuous (fun z : Iv H => (z : ℝ≥0)) := continuous_subtype_val
  have hc_tail : Tendsto (fun k => ∫ z, c k (z : ℝ≥0) ∂(ν t : Measure (Iv H))) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (ν t : Measure (Iv H)))
      (F := fun k (z : Iv H) => c k (z : ℝ≥0)) (f := fun _ => 0) (fun _ => 1)
      (fun k => ((c k).continuous.comp hval).aestronglyMeasurable) (integrable_const 1)
      (fun k => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hc01 k z).1]; exact (hc01 k z).2)
      (Eventually.of_forall fun z => by
        obtain ⟨k0, hk0⟩ := hacof ((z : ℝ≥0) : ℝ) (by rw [ENNReal.ofReal_coe_nnreal]; exact z.2)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop k0] with k hk
        rw [hc_apply, chi_one _ _ (hamono (Nat.lt_succ_self k)) _
          (hk0.trans (hamono.monotone hk))]
        ring)
    simpa using this
  obtain ⟨k, hk⟩ := (hc_tail.eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / (4 * (M + 1)) by positivity))).exists
  set g := gext f (a k) (a (k + 1)) (haH (k + 1)) with hg
  have hG := (hint' g).continuousAt (x := t)
  have hC := (hint' (c k)).continuousAt (x := t)
  rw [ContinuousAt, Metric.tendsto_nhds] at hG hC
  have hdec : ∀ s', |∫ z, f z ∂(ν s' : Measure (Iv H)) - ∫ z, g (z : ℝ≥0) ∂(ν s' : Measure (Iv H))|
      ≤ M * ∫ z, c k (z : ℝ≥0) ∂(ν s' : Measure (Iv H)) := by
    intro s'
    have hgi : Integrable (fun z : Iv H => g (z : ℝ≥0)) (ν s' : Measure (Iv H)) :=
      (g.compContinuous ⟨_, hval⟩).integrable _
    have hci : Integrable (fun z : Iv H => c k (z : ℝ≥0)) (ν s' : Measure (Iv H)) :=
      ((c k).compContinuous ⟨_, hval⟩).integrable _
    rw [← integral_sub (f.integrable _) hgi, ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hci.const_mul M) (Eventually.of_forall fun z => ?_)
    rw [hg, gext_apply f _ _ (hamono (Nat.lt_succ_self k)) (ha0 _) _ z]
    have hcz : f z - chi (a k) (a (k + 1)) z * f z = c k z * f z := by
      rw [hc_apply]; ring
    rw [hcz, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hc01 k z).1, mul_comm]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm z) (hc01 k z).1
  filter_upwards [hG (ε / 4) (by positivity), hC (ε / (4 * (M + 1))) (by positivity)]
    with s hs1 hs2
  rw [Real.dist_eq] at hs1 hs2 ⊢
  have h1 := hdec s
  have h2 := hdec t
  have hkt : ∫ z, c k (z : ℝ≥0) ∂(ν t : Measure (Iv H)) < ε / (4 * (M + 1)) := hk
  have hcs : ∫ z, c k (z : ℝ≥0) ∂(ν s : Measure (Iv H)) < 2 * (ε / (4 * (M + 1))) := by
    have := (abs_lt.1 hs2).2; linarith
  have hMε : M * (ε / (4 * (M + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb1 : M * ∫ z, c k (z : ℝ≥0) ∂(ν s : Measure (Iv H)) ≤ 2 * (ε / 4) := by
    have := mul_le_mul_of_nonneg_left hcs.le hM0
    nlinarith
  have hb2 : M * ∫ z, c k (z : ℝ≥0) ∂(ν t : Measure (Iv H)) ≤ ε / 4 :=
    (mul_le_mul_of_nonneg_left hkt.le hM0).trans hMε
  have := abs_sub_lt_iff.1 hs1
  rw [abs_lt]
  constructor
  · linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, (abs_le.1 h2).1, (abs_le.1 h2).2]
  · linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, (abs_le.1 h2).1, (abs_le.1 h2).2]

end P3


/-! ### P4. Continuity of the right-hand side of (46)/(47) -/

section P4
variable {H : ℝ≥0∞}

lemma extPath_eq (x : ℝ≥0 → ℝ) (hx0 : x 0 = 0) : extPath x = fun s => x s.toNNReal := by
  funext s
  unfold extPath
  split_ifs with h
  · rw [Real.toNNReal_of_nonpos h.le, hx0]
  · rfl

lemma ratio_le (G : ℝ → ℝ) (hGm : Monotone G) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1) (r s : ℝ)
    (hrs : r ≤ s) : |(1 - G s) / (1 - G r)| ≤ 1 := by
  rcases eq_or_ne (1 - G r) 0 with h0 | h0
  · simp [h0]
  · have hpos : 0 < 1 - G r := lt_of_le_of_ne (by linarith [(hG r).2]) h0.symm
    rw [abs_le, le_div_iff₀ hpos, div_le_iff₀ hpos]
    constructor <;> nlinarith [hGm hrs, (hG s).2, (hG s).1, (hG r).1]

lemma contA (G : ℝ → ℝ) (hGm : Monotone G) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hGc : Continuous G) (ν0 : FiniteMeasure (Iv H)) (g : ℝ≥0 →ᵇ ℝ) :
    Continuous (fun t : ℝ≥0 =>
      pair (fun x => g (x.toNNReal + t) * (1 - G (x + t)) / (1 - G x)) ν0) := by
  unfold pair
  simp only [Real.toNNReal_coe]
  have hcoe : Measurable (fun z : Iv H => ((z : ℝ≥0) : ℝ)) :=
    (NNReal.continuous_coe.comp continuous_subtype_val).measurable
  refine continuous_of_dominated (bound := fun _ => ‖g‖) (fun t => ?_) (fun t => ?_)
    (integrable_const _) (Eventually.of_forall fun z => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.div (Measurable.mul ?_ ?_) ?_
    · exact (g.continuous.comp (continuous_subtype_val.add continuous_const)).measurable
    · exact measurable_const.sub (hGm.measurable.comp (hcoe.add measurable_const))
    · exact measurable_const.sub (hGm.measurable.comp hcoe)
  · refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, mul_div_assoc, abs_mul]
    have h1 : |g ((z : ℝ≥0) + t)| ≤ ‖g‖ := g.norm_coe_le_norm _
    have h2 := ratio_le G hGm hG ((z : ℝ≥0) : ℝ) (((z : ℝ≥0) : ℝ) + t) (by simp)
    have h3 : 0 ≤ ‖g‖ := norm_nonneg _
    nlinarith [abs_nonneg (g ((z : ℝ≥0) + t)),
      abs_nonneg ((1 - G (((z : ℝ≥0) : ℝ) + t)) / (1 - G ((z : ℝ≥0) : ℝ)))]
  · exact ((g.continuous.comp (continuous_const.add continuous_id)).mul
      (continuous_const.sub (hGc.comp (continuous_const.add NNReal.continuous_coe)))).div_const _

lemma contS (G : ℝ → ℝ) (hGm : Monotone G) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hGc : Continuous G) (Kp : ℝ≥0 → ℝ) (hK : Continuous Kp) (hK0 : Kp 0 = 0)
    (g : ℝ≥0 →ᵇ ℝ) :
    Continuous (fun t : ℝ≥0 =>
      stieltjesInt Kp (fun u => g (t - u.toNNReal) * (1 - G ((t : ℝ) - u))) t) := by
  unfold stieltjesInt
  split_ifs with h
  swap
  · exact continuous_const
  set m := h.stieltjesFunction.measure with hm
  have hcont : Continuous (extPath Kp) := by
    rw [extPath_eq Kp hK0]; exact hK.comp continuous_real_toNNReal
  have hsf : ∀ s, h.stieltjesFunction s = extPath Kp s := fun s => by
    rw [Monotone.stieltjesFunction_eq]
    exact (hcont.continuousAt.continuousWithinAt).rightLim_eq
  have hsfc : Continuous h.stieltjesFunction := by
    have : (h.stieltjesFunction : ℝ → ℝ) = extPath Kp := funext hsf
    rw [this]; exact hcont
  have hsing : ∀ u, m {u} = 0 := fun u => by
    rw [hm, StieltjesFunction.measure_singleton,
      (hsfc.continuousAt.continuousWithinAt).leftLim_eq]
    simp
  rw [continuous_iff_continuousAt]
  intro s0
  set T : ℝ := (s0 : ℝ) + 1 with hT
  have hfinT : IsFiniteMeasure (m.restrict (Set.Icc 0 T)) := by
    constructor
    rw [Measure.restrict_apply_univ, hm, StieltjesFunction.measure_Icc]
    exact ENNReal.ofReal_lt_top
  set Fu : ℝ≥0 → ℝ → ℝ := fun s u => g (s - u.toNNReal) * (1 - G ((s : ℝ) - u)) with hFu
  set F' : ℝ≥0 → ℝ → ℝ := fun s u => (Set.Icc 0 (s : ℝ)).indicator (Fu s) u with hF'
  have hFum : ∀ s, Measurable (Fu s) := fun s =>
    ((g.continuous.comp (continuous_const.sub continuous_real_toNNReal)).measurable).mul
      (measurable_const.sub (hGm.measurable.comp (measurable_const.sub measurable_id)))
  have heqS : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      ∫ u in Set.Icc 0 (s : ℝ), Fu s u ∂m = ∫ u, F' s u ∂(m.restrict (Set.Icc 0 T)) := by
    intro s hs
    simp only [hF']
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl hs)]
  have hbound : ∀ s u, ‖F' s u‖ ≤ ‖g‖ := by
    intro s u
    simp only [hF']
    by_cases hu : u ∈ Set.Icc 0 (s : ℝ)
    · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_mul]
      have h1 : |g (s - u.toNNReal)| ≤ ‖g‖ := g.norm_coe_le_norm _
      have h2 : |1 - G ((s : ℝ) - u)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hG ((s : ℝ) - u)]
      nlinarith [abs_nonneg (g (s - u.toNNReal)), abs_nonneg (1 - G ((s : ℝ) - u)),
        norm_nonneg g]
    · rw [Set.indicator_of_notMem hu]; simp
  have hcA : ContinuousAt (fun s => ∫ u, F' s u ∂(m.restrict (Set.Icc 0 T))) s0 := by
    refine continuousAt_of_dominated (bound := fun _ => ‖g‖)
      (Eventually.of_forall fun s => ((hFum s).indicator measurableSet_Icc).aestronglyMeasurable)
      (Eventually.of_forall fun s => Eventually.of_forall fun u => hbound s u)
      (integrable_const _) ?_
    have hne : ∀ᵐ u ∂(m.restrict (Set.Icc 0 T)), u ≠ (s0 : ℝ) := by
      have h0 : (m.restrict (Set.Icc 0 T)) {(s0 : ℝ)} = 0 := by
        rw [Measure.restrict_apply (measurableSet_singleton _)]
        exact measure_mono_null Set.inter_subset_left (hsing _)
      rw [ae_iff]
      have hset : {a : ℝ | ¬(a ≠ (s0 : ℝ))} = {(s0 : ℝ)} := by ext; simp
      rw [hset]; exact h0
    filter_upwards [hne] with u hu
    have hcontF : Continuous (fun s : ℝ≥0 => Fu s u) :=
      (g.continuous.comp (continuous_id.sub continuous_const)).mul
        (continuous_const.sub (hGc.comp (NNReal.continuous_coe.sub continuous_const)))
    rcases lt_or_gt_of_ne hu with hlt | hgt
    · -- u < s0
      by_cases hu0 : 0 ≤ u
      · refine hcontF.continuousAt.congr ?_
        have : {s : ℝ≥0 | u < (s : ℝ)} ∈ 𝓝 s0 :=
          (isOpen_lt continuous_const NNReal.continuous_coe).mem_nhds hlt
        filter_upwards [this] with s hs
        simp only [hF']
        rw [Set.indicator_of_mem (show u ∈ Set.Icc 0 (s : ℝ) from ⟨hu0, le_of_lt hs⟩)]
      · refine (continuousAt_const (y := (0 : ℝ))).congr (Eventually.of_forall fun s => ?_)
        simp only [hF']
        rw [Set.indicator_of_notMem (fun h' => hu0 h'.1)]
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      have : {s : ℝ≥0 | (s : ℝ) < u} ∈ 𝓝 s0 :=
        (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hgt
      filter_upwards [this] with s hs
      simp only [hF']
      rw [Set.indicator_of_notMem (fun h' => by linarith [h'.2])]
  refine hcA.congr ?_
  have : {s : ℝ≥0 | (s : ℝ) < T} ∈ 𝓝 s0 :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds (by simp [hT])
  filter_upwards [this] with s hs
  exact (heqS s hs.le).symm

lemma meas_cont (G : ℝ → ℝ) (hGm : Monotone G) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hGc : Continuous G) (Kp : ℝ≥0 → ℝ) (hK : Continuous Kp) (hK0 : Kp 0 = 0)
    (hH : 0 < H) (ν : ℝ≥0 → FiniteMeasure (Iv H))
    (heq : ∀ (f : ℝ≥0 →ᵇ ℝ) (t : ℝ≥0), pair (fun x => f x.toNNReal) (ν t) =
      pair (fun x => f (x.toNNReal + t) * (1 - G (x + t)) / (1 - G x)) (ν 0) +
        stieltjesInt Kp (fun u => f (t - u.toNNReal) * (1 - G ((t : ℝ) - u))) t) :
    Continuous ν := by
  refine weak_cont hH ν fun g => ?_
  have : (fun s => pair (fun x => g x.toNNReal) (ν s)) = fun s =>
      pair (fun x => g (x.toNNReal + s) * (1 - G (x + s)) / (1 - G x)) (ν 0) +
        stieltjesInt Kp (fun u => g (s - u.toNNReal) * (1 - G ((s : ℝ) - u))) s :=
    funext fun s => heq g s
  rw [this]
  exact (contA G hGm hG hGc (ν 0) g).add (contS G hGm hG hGc Kp hK hK0 g)

end P4

end PuhaWardFluid.Limit.L2iaux

open PuhaWardFluid.Limit PuhaWardFluid.Limit.L2iaux

theorem solution {J : ℕ} (L : ClassLaws J) (E : ℝ≥0 → Fin J → ℝ) (y : ℝ≥0 → Xsp L)
    (hsol : IsFluidSol L E y) (hE : Continuous E)
    (hK : ∀ j, Continuous fun t => flK L y t j) :
    Continuous y ∧ AuxContinuous L y := by
  obtain ⟨hEup, hF, -, h45, h46, h47⟩ := hsol
  have hD : ∀ j, Continuous (fun t => flD L y t j) := fun j =>
    cont_lint (fun u => lpair (L.hs j) (flNu L y u.toNNReal j)) (fun t => ((hF.2 t).2.2 j).1)
  have hR : ∀ j, Continuous (fun t => flR L y t j) := by
    intro j
    refine cont_lint (fun u => ∫⁻ z in Set.Icc (0 : ℝ) (flQ L y u.toNNReal j),
      hazardE (L.gr j) (FcdfInv (flEta L y u.toNNReal j) z)) (fun t => ?_)
    refine lt_of_le_of_lt (lintegral_mono fun u => inner_le _ (L.gr j) (L.gr_meas j) _ ?_)
      ((hF.2 t).2.2 j).2
    have := ((hF.2 u.toNNReal).1 j)
    unfold flQ
    linarith [this.2]
  have hEj : ∀ j, Continuous (fun t => E t j) := fun j => (continuous_apply j).comp hE
  have hX : ∀ j, Continuous (fun t => flX L y t j) := by
    intro j
    have : (fun t => flX L y t j) = fun t => flX L y 0 j + E t j - flR L y t j - flD L y t j :=
      funext (h45 j)
    rw [this]
    exact ((continuous_const.add (hEj j)).sub (hR j)).sub (hD j)
  have hB : ∀ j, Continuous (fun t => flB L y t j) := by
    intro j
    have : (fun t => flB L y t j) = fun t => flK L y t j - flD L y t j + flB L y 0 j :=
      funext fun t => by unfold flK; ring
    rw [this]
    exact ((hK j).sub (hD j)).add continuous_const
  have hQc : ∀ j, Continuous (fun t => flQ L y t j) := fun j => (hX j).sub (hB j)
  have hI : Continuous (flI L y) := by
    show Continuous (fun t => 1 - ∑ j, flB L y t j)
    exact continuous_const.sub (continuous_finset_sum _ fun j _ => hB j)
  have hK0 : ∀ j, flK L y 0 j = 0 := by
    intro j
    simp only [flK, flD, flDInt, NNReal.coe_zero, Set.Icc_self]
    rw [Measure.restrict_singleton]
    simp
  have hnu : ∀ j, Continuous (fun t => flNu L y t j) := by
    intro j
    have hs := cdf_props (L.gs j) (le_of_eq (L.gs_total j))
    exact meas_cont (L.Gs j) hs.1 hs.2
      (cdf_cont (L.gs j) (L.gs_meas j) (le_of_eq (L.gs_total j)) (L.gs_neg j))
      (fun s => flK L y s j) (hK j) (hK0 j)
      (edge_pos (L.gs j) (L.gs_meas j) (le_of_eq (L.gs_total j)) (L.gs_neg j))
      (fun t => flNu L y t j) (fun f t => h46 j f t)
  have heta : ∀ j, Continuous (fun t => flEta L y t j) := by
    intro j
    have hs := cdf_props (L.gr j) (L.gr_total j)
    have hE0 : E 0 j = 0 := by rw [hEup.2.2]; rfl
    exact meas_cont (L.Gr j) hs.1 hs.2
      (cdf_cont (L.gr j) (L.gr_meas j) (L.gr_total j) (L.gr_neg j))
      (fun s => E s j) (hEj j) hE0
      (edge_pos (L.gr j) (L.gr_meas j) (L.gr_total j) (L.gr_neg j))
      (fun t => flEta L y t j) (fun f t => h47 j f t)
  refine ⟨?_, fun j => ⟨hB j, hQc j, hR j, hD j, hK j⟩, hI⟩
  have : y = fun t => ((fun j => flX L y t j), (fun j => flNu L y t j),
      (fun j => flEta L y t j)) := rfl
  rw [this]
  exact (continuous_pi hX).prodMk ((continuous_pi hnu).prodMk (continuous_pi heta))
