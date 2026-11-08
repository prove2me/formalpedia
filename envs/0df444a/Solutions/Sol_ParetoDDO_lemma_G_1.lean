-- Prove2me | solution 1 for ParetoDDO.lemma_G_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:23:45.073193+00:00
-- url     : https://prove2.me/submissions/0e106b25-f4ad-4700-870b-5be5bcfa5670

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

open ParetoDDO in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → ℝ) (zinf zbar : Ω → ℝ)
    (hz : ∀ T, 1 ≤ T → Measurable (z T)) (hzinf : Measurable zinf) (hzbar : Measurable zbar)
    (hconv : TendstoInMeasure μ z atTop zinf)
    (hdom : ∀ T, 1 ≤ T → ∀ᵐ ω ∂μ, |z T ω| ≤ zbar ω) (hint : Integrable zbar μ) :
    Tendsto (fun T => ∫ ω, z T ω ∂μ) atTop (𝓝 (∫ ω, zinf ω ∂μ)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hlim : Tendsto (fun n => ns (ms n)) atTop atTop := hns.comp hms.tendsto_atTop
  have hev : ∀ᶠ n in atTop, 1 ≤ ns (ms n) := hlim.eventually_ge_atTop 1
  exact tendsto_integral_filter_of_dominated_convergence zbar
    (hev.mono fun n hn => (hz _ hn).aestronglyMeasurable)
    (hev.mono fun n hn => (hdom _ hn).mono fun ω h => by rwa [Real.norm_eq_abs])
    hint hae
