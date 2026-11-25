-- Prove2me | solution 1 for PI.QuotMeasUniqW.qLift_isMulLeftInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:47.473728+00:00
-- url     : https://prove2.me/submissions/f86c4231-6f47-4a06-b1c4-703215d45585

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_hAvg_out
import Theorems.Thm_PI_QuotMeasUniqW_measurable_hAvg_out
import Theorems.Thm_PI_QuotMeasUniqW_lintegral_qLift
import Theorems.Thm_PI_QuotMeasUniqW_measurable_smul_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant] (ρ : Measure (G ⧸ H))
    (hρg : ∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) :
    (qLift ν ρ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have hmap : Measure.map (fun y : G ⧸ H => g • y) ρ = ρ := by
    ext s hs
    rw [Measure.map_apply (measurable_smul_quot g) hs]
    exact hρg g s hs
  have key : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂Measure.map (fun x => g * x) (qLift ν ρ) = ∫⁻ x, f x ∂qLift ν ρ := by
    intro f hf
    have hfg : Measurable (fun x => f (g * x)) := hf.comp (measurable_const_mul g)
    have hF : Measurable (fun y : G ⧸ H => hAvg ν f y.out) :=
      measurable_hAvg_out ν hf
    have hpt : ∀ y : G ⧸ H,
        hAvg ν (fun x => f (g * x)) y.out = hAvg ν f (g • y).out := by
      intro y
      have h1 : hAvg ν (fun x => f (g * x)) y.out = hAvg ν f (g * y.out) := by
        simp only [hAvg, mul_assoc]
      have h2 : (g • y : G ⧸ H) = ((g * y.out : G) : G ⧸ H) := by
        calc (g • y : G ⧸ H) = g • ((y.out : G) : G ⧸ H) := by
              rw [QuotientGroup.out_eq']
          _ = ((g * y.out : G) : G ⧸ H) := by
              rfl
      rw [h1, h2, hAvg_out]
    calc ∫⁻ x, f x ∂Measure.map (fun x => g * x) (qLift ν ρ)
        = ∫⁻ x, f (g * x) ∂qLift ν ρ := lintegral_map hf (measurable_const_mul g)
      _ = ∫⁻ y, hAvg ν (fun x => f (g * x)) y.out ∂ρ := lintegral_qLift ν ρ hfg
      _ = ∫⁻ y, hAvg ν f (g • y).out ∂ρ := lintegral_congr hpt
      _ = ∫⁻ y, hAvg ν f y.out ∂Measure.map (fun y : G ⧸ H => g • y) ρ :=
          (lintegral_map hF (measurable_smul_quot (H := H) g)).symm
      _ = ∫⁻ y, hAvg ν f y.out ∂ρ := by rw [hmap]
      _ = ∫⁻ x, f x ∂qLift ν ρ := (lintegral_qLift ν ρ hf).symm
  ext s hs
  have e1 := lintegral_indicator_one (μ := Measure.map (fun x => g * x) (qLift ν ρ)) hs
  have e2 := lintegral_indicator_one (μ := qLift ν ρ) hs
  rw [← e1, ← e2]
  exact key _ (measurable_one.indicator hs)
end PI.QuotMeasUniqW
