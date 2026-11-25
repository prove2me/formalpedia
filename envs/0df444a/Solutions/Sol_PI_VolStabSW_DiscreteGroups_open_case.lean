-- Prove2me | solution 1 for PI.VolStabSW.DiscreteGroups.open_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:51.30748+00:00
-- url     : https://prove2.me/submissions/71f346e9-cd60-4d9d-940d-00dfc85a186f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
import Theorems.Thm_PI_VolStabSW_DiscreteGroups_approx
import Theorems.Thm_PI_VolStabSW_DiscreteGroups_cc_case

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabSW PI.VolStabSW.Glue
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]
variable {X Y : Type} [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
  (hf : Continuous f) (hι : IsClosedEmbedding ι) (hr : ∀ v, f v ∈ Set.range ι) (hU : IsOpen U)
  (h0 : ∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) (h2 : ∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤)
  (h3 : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν)
include hf hι hr hU h0 h2 h3
namespace PI.VolStabSW.DiscreteGroups
theorem _root_.solution (O : Set V) (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable (fun b => fib b O) ∧ μ O = ∫⁻ b, fib b O ∂ν := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := approx O hO
  have hcc : ∀ k, IsCcOn U (φ k) := fun k => ⟨(hφ k).1, (hφ k).2.1, (hφ k).2.2.trans hOU⟩
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have hfibO : ∀ b, fib b O = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro b
    rw [← lintegral_iSup hmeas hmon]
    simp_rw [hlim]
    rw [lintegral_indicator_one hO.measurableSet]
  have hk : ∀ k, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro k
    have : (fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b)) =
        fun b => ENNReal.ofReal (∫ v, φ k v ∂(fib b)) :=
      funext fun b => (ofReal_integral_eq_lintegral_ofReal ((h3 _ (hcc k)).1 b)
        (ae_of_all _ fun v => (h01 k v).1)).symm
    rw [this]
    exact ENNReal.measurable_ofReal.comp (h3 _ (hcc k)).2.1.measurable
  have hmonb : Monotone fun k b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) :=
    fun i j hij b => lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hmono v hij)
  refine ⟨?_, ?_⟩
  · simp_rw [hfibO]
    exact Measurable.iSup hk
  · calc μ O = ∫⁻ v, O.indicator 1 v ∂μ := (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂μ := by simp_rw [hlim]
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂μ := lintegral_iSup hmeas hmon
      _ = ⨆ k, ∫⁻ b, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := by
          congr 1; funext k
          exact cc_case hf hι hr hU h0 h2 h3 (φ k) (hcc k) fun v => (h01 k v).1
      _ = ∫⁻ b, ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := (lintegral_iSup hk hmonb).symm
      _ = ∫⁻ b, fib b O ∂ν := by simp_rw [hfibO]
end PI.VolStabSW.DiscreteGroups
