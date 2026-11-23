-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.mem_pI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:13.761805+00:00
-- url     : https://prove2.me/submissions/ad0dbc74-63a8-4acd-8089-4077b1f927ae

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {hϖ : ϖ ∈ O} (x : O) : x ∈ pI O ϖ hϖ ↔ ∃ o ∈ O, (x : F) = ϖ * o := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, c.2, by rw [← hc]; exact mul_comm _ _⟩
  · rintro ⟨o, ho, e⟩
    exact ⟨⟨o, ho⟩, Subtype.ext (by show (o * ϖ : F) = x; rw [e, mul_comm])⟩
end PI.DatumBlockEigen.Unit
