-- Prove2me | solution 1 for QuantileMDP.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-13T17:50:58.485198+00:00
-- url     : https://prove2.me/submissions/d65692b8-ebda-4d99-8041-53616fd9f774

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Instances.EReal.Lemmas
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory Set Filter QuantileMDP
open scoped Topology ENNReal

private theorem tendsto_closed_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Tendsto (fun y => μ (Iic y)) (𝓝[>] x) (𝓝 (μ (Iic x))) := by
  have hset : (⋂ y > x, Iic y) = Iic x := by
    ext z
    simp only [mem_iInter, mem_Iic]
    exact ⟨fun h => le_of_not_gt fun hz =>
      let ⟨y, hxy, hyz⟩ := exists_between hz
      (not_le_of_gt hyz) (h y hxy), fun h y hy => h.trans hy.le⟩
  rw [← hset]
  exact tendsto_measure_biInter_gt (fun _ _ => measurableSet_Iic.nullMeasurableSet)
    (fun _ _ _ h => Iic_subset_Iic.mpr h) ⟨x + 1, by linarith, measure_ne_top μ _⟩

private theorem positive_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    quantile μ τ ≤ (x : EReal) ↔ ENNReal.ofReal τ ≤ μ (Iic x) := by
  have hdef : quantile μ τ =
      sInf ((fun y : ℝ => (y : EReal)) '' {y : ℝ | ENNReal.ofReal τ ≤ μ (Iic y)}) := by
    rw [quantile, if_neg hτ.ne']
    split_ifs with he
    · subst τ
      congr 2
      ext y
      simp only [mem_ofPred_eq, ENNReal.ofReal_one]
      exact ⟨fun h => h.ge, fun h => le_antisymm prob_le_one h⟩
    · rfl
  rw [hdef]
  refine ⟨?_, fun hx => sInf_le ⟨x, hx, rfl⟩⟩
  intro hx
  by_contra! h
  have he := (tendsto_order.mp (tendsto_closed_tail μ x)).2 _ h
  obtain ⟨y, hy, hyx⟩ := (he.and (@self_mem_nhdsWithin _ _ x (Ioi x))).exists
  have hyinf : (y : EReal) ≤ sInf ((fun z : ℝ => (z : EReal)) ''
      {z : ℝ | ENNReal.ofReal τ ≤ μ (Iic z)}) := by
    refine le_sInf ?_
    rintro _ ⟨z, hz, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (le_of_not_gt fun hzy =>
      (not_le_of_gt hy) (hz.trans (measure_mono (Iic_subset_Iic.mpr hzy.le))))
  exact (not_le_of_gt (EReal.coe_lt_coe_iff.mpr hyx)) (hyinf.trans hx)

private theorem zero_quantile_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {τ : ℝ} (hτ : 0 < τ) : quantile μ 0 ≤ quantile μ τ := by
  rw [quantile, if_pos rfl]
  refine sSup_le ?_
  rintro _ ⟨d, hd, rfl⟩
  by_contra! h
  obtain ⟨x, hx, hxd⟩ := EReal.exists_between_coe_real h
  have hcx := (positive_quantile μ hτ x).mp hx.le
  have hc : μ (Iio d) = 0 := by
    have hmass := prob_add_prob_compl (μ := μ) (measurableSet_Iio (a := d))
    rw [compl_Iio, hd] at hmass
    exact (ENNReal.add_left_inj (by simp : (1 : ℝ≥0∞) ≠ ⊤)).mp (hmass.trans (zero_add _).symm)
  have hx0 : μ (Iic x) = 0 :=
    measure_mono_null (Iic_subset_Iio.mpr (EReal.coe_lt_coe_iff.mp hxd)) hc
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hτ)) (hx0 ▸ hcx)

/-- The generalized inverse of the CDF is monotone and left continuous,
and the closed lower tail at the quantile carries at least the specified mass. -/
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MonotoneOn (quantile μ) (Icc 0 1) ∧
      (∀ τ ∈ Ioc (0 : ℝ) 1, ContinuousWithinAt (quantile μ) (Icc 0 τ) τ) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, ENNReal.ofReal τ ≤ μ {x : ℝ | (x : EReal) ≤ quantile μ τ}) := by
  have hmono : MonotoneOn (quantile μ) (Icc 0 1) := by
    intro u hu v hv huv
    rcases eq_or_lt_of_le hv.1 with hv0 | hv0
    · have hu0 : u = v := le_antisymm huv (hv0 ▸ hu.1)
      rw [hu0]
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · rw [← hu0]
      exact zero_quantile_le μ hv0
    by_contra! h
    obtain ⟨x, hxv, hxu⟩ := EReal.exists_between_coe_real h
    have hcx := (positive_quantile μ hv0 x).mp hxv.le
    exact (not_le_of_gt hxu) ((positive_quantile μ hu0 x).mpr ((ENNReal.ofReal_le_ofReal huv).trans hcx))
  refine ⟨hmono, ?_, ?_⟩
  · intro τ hτ
    refine tendsto_order.mpr ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨x, hbx, hx⟩ := EReal.exists_between_coe_real hb
      have hcx : (μ (Iic x)).toReal < τ :=
        (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ _)).mp <|
        lt_of_not_ge fun h => (not_le_of_gt hx) ((positive_quantile μ hτ.1 x).mpr h)
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hcx),
        @self_mem_nhdsWithin _ _ τ (Icc 0 τ)] with u hcu hu
      have hu0 : 0 < u := ENNReal.toReal_nonneg.trans_lt hcu
      exact hbx.trans (lt_of_not_ge fun h =>
        (not_le_of_gt ((ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ _)).mpr hcu))
          ((positive_quantile μ hu0 x).mp h))
    · filter_upwards [@self_mem_nhdsWithin _ _ τ (Icc 0 τ)] with u hu
      exact (hmono ⟨hu.1, hu.2.trans hτ.2⟩ ⟨hτ.1.le, hτ.2⟩ hu.2).trans_lt hb
  · intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with h | h
    · rw [← h, ENNReal.ofReal_zero]
      exact bot_le
    by_cases ht : quantile μ τ = ⊤
    · simp [ht, ENNReal.ofReal_le_one.mpr hτ.2]
    have hb : quantile μ τ ≠ ⊥ := by
      have hlim : Tendsto (fun x : ℝ => μ (Iic x)) atBot (𝓝 0) := by
        have hlim := tendsto_measure_iInter_atBot (μ := μ)
          (s := fun x : ℝ => Iic x) (fun _ => measurableSet_Iic.nullMeasurableSet)
          monotone_Iic ⟨0, measure_ne_top μ _⟩
        have hempty : (⋂ x : ℝ, Iic x) = ∅ := by
          ext y
          simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
          exact fun hy => (not_le_of_gt (sub_lt_self y zero_lt_one)) (hy (y - 1))
        simpa [hempty, Function.comp_def] using hlim
      obtain ⟨x, hx⟩ := ((tendsto_order.mp hlim).2 _ (ENNReal.ofReal_pos.mpr h)).exists
      intro he
      exact (not_le_of_gt hx) ((positive_quantile μ h x).mp (he ▸ bot_le))
    let x := (quantile μ τ).toReal
    have hx : (x : EReal) = quantile μ τ := EReal.coe_toReal ht hb
    rw [← hx, show {y : ℝ | (y : EReal) ≤ (x : EReal)} = Iic x by
      ext y; exact EReal.coe_le_coe_iff]
    exact (positive_quantile μ h x).mp hx.ge
