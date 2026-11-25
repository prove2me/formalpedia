-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.mk_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:34.149269+00:00
-- url     : https://prove2.me/submissions/d6fd356a-250c-4536-83d7-aaa9e1ac79ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {u : F} (hu : u ∈ O) (o : F) (ho : o ∈ O) (h : u = ϖ * o) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨u, hu⟩ : O) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨⟨o, ho⟩, Subtype.ext (by simp [h, mul_comm])⟩
end PI.ParahoricIdxZ.W
