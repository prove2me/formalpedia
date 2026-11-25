-- Prove2me | solution 1 for PI.AprimeInfW.chart_change_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:07.42704+00:00
-- url     : https://prove2.me/submissions/4636ce9f-e474-4faf-a01d-a14282f7523f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ChartChg

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
open MeasureTheory Topology
namespace PI.AprimeInfW
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (ψ : E → E) (ψ' : E → E →L[ℝ] E) (x₀ : E) (hψ : ContinuousAt ψ x₀)
    (hf : ContinuousAt f (ψ x₀)) (hd : ContinuousAt (fun p => (ψ' p).det) x₀) :
    ContinuousAt (fun p => |(ψ' p).det| * f (ψ p)) x₀ := (continuous_abs.continuousAt.comp hd).mul (hf.comp hψ)
end PI.AprimeInfW
