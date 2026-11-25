-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfConv.integral_comp_homeo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:16.565676+00:00
-- url     : https://prove2.me/submissions/0e3c0ce3-c437-479b-a20d-c61f2b5782da

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) (e : G ≃ₜ G) (he : MeasurePreserving e μ μ) (f : G → E) :
    ∫ x, f (e x) ∂μ = ∫ x, f x ∂μ :=
  he.integral_comp e.measurableEmbedding f
end PI.UnitaryGroupMassFormula.GelfConv
