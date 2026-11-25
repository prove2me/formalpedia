-- Prove2me | solution 1 for PI.RhsWLim.W.lint_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:41.939642+00:00
-- url     : https://prove2.me/submissions/bc1f7a04-b239-42f3-a395-131bb717163c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (P : ℝ → ℝ≥0∞) (hP : Measurable P) (hper : ∀ θ, P (θ + 2 * Real.pi) = P θ) :
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), P θ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, P θ := by
  have hπ := Real.pi_pos
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume))]
  have h1 : Set.Ioc 0 (2 * Real.pi) = Set.Ioc 0 Real.pi ∪ Set.Ioc Real.pi (2 * Real.pi) :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have h2 : Set.Ioc (-Real.pi) Real.pi = Set.Ioc (-Real.pi) 0 ∪ Set.Ioc 0 Real.pi :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  rw [h1, h2, lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl),
    lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl), add_comm]
  congr 1
  have hmp : MeasurePreserving (fun x : ℝ => x + 2 * Real.pi) volume volume := measurePreserving_add_right volume _
  have hpre : (fun x : ℝ => x + 2 * Real.pi) ⁻¹' Set.Ioc Real.pi (2 * Real.pi) = Set.Ioc (-Real.pi) 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨a, b⟩; constructor <;> linarith
    · rintro ⟨a, b⟩; constructor <;> linarith
  have := hmp.setLIntegral_comp_preimage (s := Set.Ioc Real.pi (2 * Real.pi)) measurableSet_Ioc hP
  rw [hpre] at this
  rw [← this]
  exact lintegral_congr fun a => hper a
end PI.RhsWLim.W
