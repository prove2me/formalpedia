-- Prove2me | solution 1 for PI.AprimeInfG.contAt_dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:18:59.865834+00:00
-- url     : https://prove2.me/submissions/e617cc0f-c16c-4baa-95c8-ee99cb5a1bab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpChartC

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
theorem _root_.solution {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {F : P → P} {F' : P → (P →L[ℝ] P)}
    {D : P → ℝ} (hF : ContinuousAt F 0) (hdet : ContinuousAt (fun p => |(F' p).det|) 0) (hD : ContinuousAt D (F 0)) :
    ContinuousAt (fun p => |(F' p).det| * D (F p)) 0 :=
  hdet.mul (ContinuousAt.comp (g := D) hD hF)
end PI.AprimeInfG
