-- Prove2me | solution 1 for ProbabilityTheory.isLevyProcess_levyJumpPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:39:17.271822+00:00
-- url     : https://prove2.me/submissions/7513aa2a-39de-4dd9-adeb-cbed960f59f2

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_increment_apply
import Theorems.Thm_ProbabilityTheory_measurable_increment
import Theorems.Thm_ProbabilityTheory_levyJumpPath_zero
import Theorems.Thm_ProbabilityTheory_levyJumpPath_ae_eq
import Theorems.Thm_ProbabilityTheory_ae_isCadlag_levyJumpPath
import Theorems.Thm_ProbabilityTheory_measurable_levyJumpPath
import Theorems.Thm_ProbabilityTheory_hasIndependentIncrements_levyJumpProcess
import Theorems.Thm_ProbabilityTheory_hasStationaryIncrements_levyJumpProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) : IsLevyProcess (levyJumpPath hd hν b) μ where
  start_zero := levyJumpPath_zero hd hν b
  indep_increments := by
    intro n τ hτmono
    have hae : ∀ k : Fin n,
        increment (levyJumpProcess hd hν b) (τ k.castSucc) (τ k.succ)
          =ᵐ[μ] increment (levyJumpPath hd hν b) (τ k.castSucc) (τ k.succ) := by
      intro k
      filter_upwards [levyJumpPath_ae_eq hd hν b (τ k.castSucc),
        levyJumpPath_ae_eq hd hν b (τ k.succ)] with ω h1 h2
      simp only [increment_apply]
      rw [h1, h2]
    exact (iIndepFun_congr hae).mp
      (hasIndependentIncrements_levyJumpProcess hd hν b n τ hτmono)
  stationary_increments := by
    intro s h
    have hmeas : ∀ u : ℝ≥0, Measurable (levyJumpPath hd hν b u) :=
      fun u => measurable_levyJumpPath hd hν b u
    have haem_incr : ∀ p q : ℝ≥0, AEMeasurable (increment (levyJumpPath hd hν b) p q) μ :=
      fun p q => (measurable_increment (hmeas p) (hmeas q)).aemeasurable
    have hae : ∀ p q : ℝ≥0,
        increment (levyJumpPath hd hν b) p q =ᵐ[μ] increment (levyJumpProcess hd hν b) p q := by
      intro p q
      filter_upwards [levyJumpPath_ae_eq hd hν b p, levyJumpPath_ae_eq hd hν b q] with ω h1 h2
      simp only [increment_apply]
      rw [h1, h2]
    exact ((IdentDistrib.of_ae_eq (haem_incr s (s + h)) (hae s (s + h))).trans
      (hasStationaryIncrements_levyJumpProcess hd hν b s h)).trans
      (IdentDistrib.of_ae_eq (haem_incr 0 h) (hae 0 h)).symm
  cadlag_ae := ae_isCadlag_levyJumpPath hd hν b
