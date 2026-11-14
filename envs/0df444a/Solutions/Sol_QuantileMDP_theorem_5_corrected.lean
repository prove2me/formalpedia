-- Prove2me | solution 1 for QuantileMDP.theorem_5_corrected
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-14T01:56:56.36034+00:00
-- url     : https://prove2.me/submissions/2317ac7c-9497-4665-8fc1-23794a008ffd

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Instances.EReal.Lemmas
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory Set Filter QuantileMDP
open scoped ENNReal Topology

namespace QuantileMDP

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

end QuantileMDP

/-- The conditional-quantile hypothesis needed by the proof of Theorem 5.
The two families of laws are mixed with the same distribution of starting
states. It is enough to compare conditional quantiles at all interior levels. -/
theorem solution {S : Type*} [Fintype S] (p : S → ℝ≥0∞)
    (μ ν : S → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hν : ∀ i, IsProbabilityMeasure (ν i))
    (h : ∀ i τ, τ ∈ Ioo (0 : ℝ) 1 → quantile (ν i) τ ≤ quantile (μ i) τ)
    (τ : ℝ) (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    quantile (∑ i, p i • ν i) τ ≤ quantile (∑ i, p i • μ i) τ := by
  have hcdf (i : S) (x : ℝ) : μ i (Iic x) ≤ ν i (Iic x) := by
    by_contra! hbad
    let := hμ i
    let := hν i
    have hlt : (ν i (Iic x)).toReal < (μ i (Iic x)).toReal :=
      (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hbad
    obtain ⟨u, hlo, hhi⟩ := exists_between hlt
    have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨ENNReal.toReal_nonneg.trans_lt hlo,
      hhi.trans_le (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using (prob_le_one :
        μ i (Iic x) ≤ 1)))⟩
    have hm : quantile (μ i) u ≤ (x : EReal) := by
      rw [quantile, if_neg hu.1.ne', if_neg hu.2.ne]
      exact sInf_le ⟨x, (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hhi.le, rfl⟩
    have hn : (x : EReal) < quantile (ν i) u :=
      lt_of_not_ge fun he => hlo.not_ge ((ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
        ((positive_quantile (ν i) hu.1 x).mp he))
    exact hn.not_ge ((h i u hu).trans hm)
  rw [quantile, if_neg hτ.1.ne', if_neg hτ.2.ne, quantile, if_neg hτ.1.ne', if_neg hτ.2.ne]
  apply sInf_le_sInf
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  change ENNReal.ofReal τ ≤ (∑ i, p i • ν i) (Iic x)
  refine (show ENNReal.ofReal τ ≤ (∑ i, p i • μ i) (Iic x) from hx).trans ?_
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcdf i x) bot_le
