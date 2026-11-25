-- Prove2me | solution 1 for PI.AprimeInfW.pi_smul_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:11.667912+00:00
-- url     : https://prove2.me/submissions/a7abfdfe-0e58-4742-b4be-83b270fbeacb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PlaceAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix
open scoped ENNReal NNReal
namespace PI.AprimeInfW
theorem _root_.solution {V : Type} [Fintype V] {X : V → Type} [∀ v, MeasurableSpace (X v)]
    (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)] (c : V → ℝ≥0) :
    Measure.pi (fun v => c v • μ v) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi μ := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Measure.smul_apply]
  rfl
end PI.AprimeInfW
