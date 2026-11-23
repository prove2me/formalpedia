-- Prove2me | solution 1 for PI.QuotInvW.weil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:09.853898+00:00
-- url     : https://prove2.me/submissions/6abeb383-797d-4b7b-b300-9ccd42b3b37f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}
variable {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
namespace PI.QuotInvW
theorem _root_.solution (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν :=
  h.2.2.2.2.2.2.2 f hf
end PI.QuotInvW
