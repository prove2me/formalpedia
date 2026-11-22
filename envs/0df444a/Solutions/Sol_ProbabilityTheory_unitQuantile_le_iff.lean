-- Prove2me | solution 1 for ProbabilityTheory.unitQuantile_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:27.819227+00:00
-- url     : https://prove2.me/submissions/a44a6533-4d74-433f-845f-c7745fba1876

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure I) [IsProbabilityMeasure μ] (t x : I) :
    unitQuantile μ t ≤ x ↔ (t : ℝ) ≤ μ.real (Iic x) := by
  constructor
  · intro ht
    by_cases hx : x = 1
    · have he : Iic x = univ := by
        ext y
        simp [hx, unitInterval.le_one']
      rw [he, probReal_univ]
      exact t.property.2
    let : NeBot (𝓝[>] x) := nhdsGT_neBot_of_exists_gt
      ⟨1, lt_of_le_of_ne unitInterval.le_one' hx⟩
    have hc : ContinuousWithinAt (fun y : I => μ.real (Iic y)) (Ioi x) x := by
      have h := continuousWithinAt_Ioi_iff_Ici.mpr
        ((cdf (μ.map ((↑) : I → ℝ))).right_continuous (x : ℝ))
      have he (y : I) : μ.real (Iic y) = cdf (μ.map ((↑) : I → ℝ)) (y : ℝ) := by
        rw [ProbabilityTheory.unitInterval.cdf_eq_real]
        congr 1
        ext z
        simp
      simp_rw [he]
      exact h.comp (continuous_subtype_val.continuousWithinAt) (fun y hy => hy)
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] x) continuousWithinAt_const hc ?_
    apply eventually_nhdsWithin_of_forall
    intro y hy
    by_contra! h
    have hyt : y ≤ unitQuantile μ t := le_sSup h
    exact (not_le.mpr hy) (hyt.trans ht)
  · intro ht
    apply sSup_le
    intro y hy
    by_contra! hxy
    have hm : μ.real (Iic x) ≤ μ.real (Iic y) := measureReal_mono (Iic_subset_Iic.mpr hxy.le)
    exact (not_lt.mpr (ht.trans hm)) hy
end ProbabilityTheory
