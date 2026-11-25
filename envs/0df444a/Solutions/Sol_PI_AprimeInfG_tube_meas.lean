-- Prove2me | solution 1 for PI.AprimeInfG.tube_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:29.523242+00:00
-- url     : https://prove2.me/submissions/4b714cbb-da7d-44dc-999f-88046058aaa7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
import Theorems.Thm_PI_AprimeInfG_mem_tubeS_mul_iff
import Theorems.Thm_PI_AprimeInfA_lintegral_mul_right_of_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.AprimeInfG
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (h0 : ν univ ≠ 0) (hfin : ν univ ≠ ∞) {V : Set G}
    (hV : ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ H → a = b) {S : Set H} (hS : MeasurableSet S)
    (hT : MeasurableSet (tubeS H V S)) (hVH : MeasurableSet (tubeS H V univ)) :
    ν univ * μ (tubeS H V S) = ν S * μ (tubeS H V univ) := by
  have hf : Measurable ((tubeS H V S).indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hT
  have hmeas2 : AEMeasurable (Function.uncurry fun (g : G) (h : H) =>
      (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G))) (μ.prod ν) :=
    (hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable).aemeasurable
  have e1 : ∫⁻ g, ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂ν ∂μ =
      ν univ * μ (tubeS H V S) := by
    rw [lintegral_lintegral_swap hmeas2]
    have : ∀ h : H, ∫⁻ g, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂μ =
        ∫⁻ g, (tubeS H V S).indicator (1 : G → ℝ≥0∞) g ∂μ := fun h =>
      PI.AprimeInfA.lintegral_mul_right_of_mem μ H ν h0 hfin h hf
    simp_rw [this]
    rw [lintegral_const, lintegral_indicator_one hT, mul_comm]
  have e2 : ∀ g, ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂ν =
      (tubeS H V univ).indicator (fun _ => ν S) g := by
    intro g
    by_cases hg : g ∈ tubeS H V univ
    · obtain ⟨a, ha, h0', -, rfl⟩ := hg
      have hm : a * (h0' : G) ∈ tubeS H V univ := ⟨a, ha, h0', mem_univ _, rfl⟩
      rw [indicator_of_mem hm]
      have hpt : ∀ h : H, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (a * (h0' : G) * (h : G)) =
          S.indicator (1 : H → ℝ≥0∞) (h0' * h) := by
        intro h
        by_cases hh : h0' * h ∈ S
        · rw [indicator_of_mem ((mem_tubeS_mul_iff H hV S ha h0' h).2 hh), indicator_of_mem hh]
          simp
        · rw [indicator_of_notMem (fun c => hh ((mem_tubeS_mul_iff H hV S ha h0' h).1 c)),
            indicator_of_notMem hh]
      calc ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (a * (h0' : G) * (h : G)) ∂ν
          = ∫⁻ h, S.indicator (1 : H → ℝ≥0∞) (h0' * h) ∂ν := lintegral_congr hpt
        _ = ∫⁻ h, S.indicator (1 : H → ℝ≥0∞) h ∂ν :=
            lintegral_mul_left_eq_self (fun h => S.indicator (1 : H → ℝ≥0∞) h) h0'
        _ = ν S := lintegral_indicator_one hS
    · rw [indicator_of_notMem hg]
      have hz : ∀ h : H, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) = 0 := by
        intro h
        apply indicator_of_notMem
        rintro ⟨a, ha, h', -, he⟩
        refine hg ⟨a, ha, h' * h⁻¹, mem_univ _, ?_⟩
        have : g = a * (h' : G) * (h : G)⁻¹ := by rw [← he]; group
        rw [this]
        simp [mul_assoc]
      simp [hz]
  calc ν univ * μ (tubeS H V S)
      = ∫⁻ g, ∫⁻ h, (tubeS H V S).indicator (1 : G → ℝ≥0∞) (g * (h : G)) ∂ν ∂μ := e1.symm
    _ = ∫⁻ g, (tubeS H V univ).indicator (fun _ => ν S) g ∂μ := lintegral_congr e2
    _ = ν S * μ (tubeS H V univ) := lintegral_indicator_const hVH _
end PI.AprimeInfG
