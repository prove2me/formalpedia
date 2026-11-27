-- Prove2me | solution 1 for PI.PhMeasCore.UnitaryGroupMassFormula.phMeasCore_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:47.42787+00:00
-- url     : https://prove2.me/submissions/6f8bac12-38b3-477f-9e4e-018ce1484537

import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_Development
import Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_isClosed_UH
import Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_continuousOn_B

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
namespace PI.PhMeasCore.UnitaryGroupMassFormula
theorem _root_.solution (hR : StepRed) (hE : StepExp) (hS : StepSub) (hW : StepWord) : PI.PhMeasCore := by
  intro n ε Hm H _ _ Wp _ _ σ B w ⟨P, hP, hPH, hσ, _⟩ hadd _ hB hw
  obtain ⟨hu, hmul⟩ := hR n ε Hm H σ P hP hPH hσ
  have hexp : ∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm :=
    fun X hX t => hE n Hm X hu hX t
  have hc : ContinuousOn (fun g => B (σ g w)) (UH Hm) :=
    continuousOn_B hS hW hmul hexp hadd hB hw
  have hof : Continuous (fun x : Fin n → Fin n → ℂ => Matrix.of x) := continuous_id
  have hcl : IsClosed {x : Fin n → Fin n → ℂ | Matrix.of x ∈ UH Hm} :=
    (isClosed_UH Hm).preimage hof
  classical
  rw [← Set.piecewise_eq_indicator]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hcl.measurableSet
  exact (hc.comp hof.continuousOn fun x hx => hx).norm
end PI.PhMeasCore.UnitaryGroupMassFormula
