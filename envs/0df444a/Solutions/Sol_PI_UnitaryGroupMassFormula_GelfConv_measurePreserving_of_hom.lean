-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.measurePreserving_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:25.325515+00:00
-- url     : https://prove2.me/submissions/43404c52-460b-40e1-b50b-4f6060a3cac5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfConv
open MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfConv
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (σ : G →* G)
    (hc : Continuous σ) (hs : Function.Surjective σ) : MeasurePreserving σ μ μ :=
  MonoidHom.measurePreserving hc hs rfl
end PI.UnitaryGroupMassFormula.GelfConv
