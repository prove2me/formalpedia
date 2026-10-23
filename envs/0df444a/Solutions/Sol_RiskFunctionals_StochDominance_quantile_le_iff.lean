-- Prove2me | solution 1 for RiskFunctionals.StochDominance.quantile_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:35:59.891987+00:00
-- url     : https://prove2.me/submissions/0401939d-fa34-42eb-b7b9-293b580bc08f

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

open MeasureTheory
open RiskFunctionals.StochDominance

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (p u : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hfin : ∃ v : ℝ, p ≤ distributionFunction μ v) :
    quantileFunction μ p ≤ u ↔ p ≤ distributionFunction μ u := by
  have hF : ∀ v, distributionFunction μ v = ProbabilityTheory.cdf μ v := fun v =>
    (ProbabilityTheory.cdf_eq_real μ v).symm
  set S := {u : ℝ | p ≤ distributionFunction μ u} with hS
  have hne : S.Nonempty := hfin
  have hbdd : BddBelow S := by
    have h := (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds hp)
    obtain ⟨L, hL⟩ := Filter.eventually_atBot.1 h
    refine ⟨L, fun v hv => ?_⟩
    by_contra hlt
    have := hL v (le_of_lt (lt_of_not_ge hlt))
    have hv' : p ≤ distributionFunction μ v := hv
    rw [hF] at hv'
    linarith
  have hmono : Monotone (distributionFunction μ) := fun a b hab => by
    rw [hF, hF]; exact (ProbabilityTheory.cdf μ).mono hab
  constructor
  · intro hq
    have hQ : p ≤ distributionFunction μ (quantileFunction μ p) := by
      have hev : ∀ᶠ v in nhdsWithin (quantileFunction μ p) (Set.Ioi (quantileFunction μ p)),
          p ≤ ProbabilityTheory.cdf μ v := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        obtain ⟨w, hwS, hwv⟩ := exists_lt_of_csInf_lt hne hv
        have : p ≤ distributionFunction μ w := hwS
        rw [← hF]; exact this.trans (hmono hwv.le)
      have ht : Filter.Tendsto (ProbabilityTheory.cdf μ)
          (nhdsWithin (quantileFunction μ p) (Set.Ioi (quantileFunction μ p)))
          (nhds (ProbabilityTheory.cdf μ (quantileFunction μ p))) :=
        ((ProbabilityTheory.cdf μ).right_continuous _).tendsto.mono_left
          (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hF]
      exact ge_of_tendsto ht hev
    exact hQ.trans (hmono hq)
  · intro hu
    exact csInf_le hbdd hu
