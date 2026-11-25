-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.cardStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:20.414117+00:00
-- url     : https://prove2.me/submissions/c0251551-60e8-48f0-9e64-3797969c9063

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal
import Theorems.Thm_PI_ParahoricIdxZ_W_span_isMaximal
import Theorems.Thm_PI_ParahoricIdxZ_W_card_GL_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
namespace PI.ParahoricIdxZ.W
theorem _root_.solution : CardStep := by
  intro F _ O ϖ hϖ hϖ0 hloc hfin n
  haveI : (Ideal.span {(⟨ϖ, hϖ⟩ : O)}).IsMaximal := span_isMaximal O ϖ hϖ hloc
  letI : Field (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) := Ideal.Quotient.field _
  letI : Fintype (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) := Fintype.ofFinite _
  have h := card_GL_real (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) n
  rw [Nat.card_eq_fintype_card (α := Formalism.DoubleCosetMeasures.kF O ϖ hϖ)]
  exact h
end PI.ParahoricIdxZ.W
