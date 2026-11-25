-- Prove2me | solution 1 for PI.DvRows.conjugate_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:23.726693+00:00
-- url     : https://prove2.me/submissions/b5c6d129-efba-4727-96b8-98270dd56b3b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_conjW_conjW
import Theorems.Thm_PI_DvRows_vAdd_conj
import Theorems.Thm_PI_DvRows_absNorm_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
namespace PI.DvRows
theorem _root_.solution : ConjPrime := by
  intro K _ _ _
  exact ⟨conjW, fun w => conjW_conjW w, fun w => ⟨fun x => vAdd_conj w x, absNorm_conj w⟩⟩
end PI.DvRows
