-- Prove2me | solution 1 for StarShapedRisk.LawInvariant.eqA1_fsd_iff_VaR_le
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T06:14:49.373893+00:00
-- url     : https://prove2.me/submissions/67a554f1-ca7c-4be1-8024-1956975701fe

import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma lr_cdf_prob (X : Positions Ω) (t : ℝ) :
    ENNReal.ofReal (cdf (P.map X.val) t) = P {ω | X.val ω ≤ t} := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  rw [ofReal_cdf, Measure.map_apply X.property.1 measurableSet_Iic]
  rfl

lemma lr_threshold (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    P {ω | t < X.val ω} ≤ ENNReal.ofReal (1-α) ↔ α ≤ cdf (P.map X.val) t := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  have hm : MeasurableSet {ω | X.val ω ≤ t} := measurableSet_le X.property.1 measurable_const
  have he : {ω | t < X.val ω} = {ω | X.val ω ≤ t}ᶜ := by ext ω; simp
  rw [he, measure_compl hm (measure_ne_top _ _), measure_univ, ← lr_cdf_prob P X t]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (cdf_nonneg _ _), ENNReal.ofReal_le_ofReal_iff (by linarith [hα.2])]
  constructor <;> intro h <;> linarith

lemma lr_quantile_bounds (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) :
    {t : ℝ | α ≤ cdf (P.map X.val) t}.Nonempty ∧
      BddBelow {t : ℝ | α ≤ cdf (P.map X.val) t} := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  obtain ⟨C,hC⟩ := X.property.2
  have hc : cdf (P.map X.val) C = 1 := by
    have he : {ω | X.val ω ≤ C} = univ := by ext ω; simp [(abs_le.mp (hC ω)).2]
    have hh := lr_cdf_prob P X C
    rw [he, measure_univ] at hh
    exact ENNReal.ofReal_eq_one.mp hh
  refine ⟨⟨C, hα.2.le.trans_eq hc.symm⟩, -C, ?_⟩
  intro t ht
  by_contra h
  have hlt : t < -C := lt_of_not_ge h
  have he : {ω | X.val ω ≤ t} = ∅ := by
    ext ω; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    linarith [(abs_le.mp (hC ω)).1]
  have hh := lr_cdf_prob P X t
  rw [he, measure_empty] at hh
  have hz : cdf (P.map X.val) t = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hh) (cdf_nonneg _ _)
  change α ≤ cdf (P.map X.val) t at ht
  rw [hz] at ht
  exact (not_le_of_gt hα.1) ht

lemma lr_quantile_le (X : Positions Ω) (α : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    VaR P α X.val ≤ t ↔ α ≤ cdf (P.map X.val) t := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  have he : {r : ℝ | P {ω | r < X.val ω} ≤ ENNReal.ofReal (1-α)} =
      {r : ℝ | α ≤ cdf (P.map X.val) r} := by ext r; exact lr_threshold P X α hα r
  have hb := lr_quantile_bounds P X α hα
  let q := sInf {r : ℝ | α ≤ cdf (P.map X.val) r}
  have hq : α ≤ cdf (P.map X.val) q := by
    have hc := ((cdf (P.map X.val)).right_continuous q).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hc
    filter_upwards [self_mem_nhdsWithin] with r hr
    obtain ⟨s, hs, hsr⟩ := (csInf_lt_iff hb.2 hb.1).mp hr
    exact hs.trans ((cdf (P.map X.val)).mono hsr.le)
  change sInf _ ≤ t ↔ _
  rw [he]
  constructor
  · intro h; exact hq.trans ((cdf (P.map X.val)).mono h)
  · intro h; exact csInf_le hb.2 h
end StarShapedRisk.LawInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
namespace StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), Eq. (A.1) (p. 2652): for bounded measurable losses `X`, `Y` on a
probability space, `F_X ≥ F_Y` pointwise if and only if `VaR_α(X) ≤ VaR_α(Y)` for all
`α ∈ (0,1)`. No atomlessness is assumed. -/
theorem eqA1_fsd_iff_VaR_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Positions Ω) :
    FSD P X.1 Y.1 ↔ ∀ α ∈ Set.Ioo (0 : ℝ) 1, VaR P α X.1 ≤ VaR P α Y.1 := by
  haveI : IsProbabilityMeasure (P.map X.val) := Measure.isProbabilityMeasure_map X.property.1.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y.val) := Measure.isProbabilityMeasure_map Y.property.1.aemeasurable
  constructor
  · intro h α hα
    apply (lr_quantile_le P X α hα _).mpr
    have hy := (lr_quantile_le P Y α hα (VaR P α Y.val)).mp le_rfl
    have hc : cdf (P.map Y.val) (VaR P α Y.val) ≤ cdf (P.map X.val) (VaR P α Y.val) := by
      apply (ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)).mp
      rw [lr_cdf_prob, lr_cdf_prob]
      exact h _
    exact hy.trans hc
  · intro h t
    rw [← lr_cdf_prob P Y t, ← lr_cdf_prob P X t]
    apply ENNReal.ofReal_le_ofReal
    by_contra hn
    have hlt : cdf (P.map X.val) t < cdf (P.map Y.val) t := lt_of_not_ge hn
    let α := (cdf (P.map X.val) t + cdf (P.map Y.val) t) / 2
    have hα0 : 0 < α := by dsimp [α]; linarith [cdf_nonneg (P.map X.val) t]
    have hα1 : α < 1 := by dsimp [α]; linarith [cdf_le_one (P.map Y.val) t]
    have hy : VaR P α Y.val ≤ t := (lr_quantile_le P Y α ⟨hα0,hα1⟩ t).mpr (by dsimp [α]; linarith)
    have hx := (lr_quantile_le P X α ⟨hα0,hα1⟩ t).mp ((h α ⟨hα0,hα1⟩).trans hy)
    dsimp [α] at hx
    linarith


end StarShapedRisk.LawInvariant


open StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), Eq. (A.1) (p. 2652): for bounded measurable losses `X`, `Y` on a
probability space, `F_X ≥ F_Y` pointwise if and only if `VaR_α(X) ≤ VaR_α(Y)` for all
`α ∈ (0,1)`. No atomlessness is assumed. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Positions Ω) :
    FSD P X.1 Y.1 ↔ ∀ α ∈ Set.Ioo (0 : ℝ) 1, VaR P α X.1 ≤ VaR P α Y.1 := by
  exact eqA1_fsd_iff_VaR_le P X Y


#check solution
#print axioms solution
