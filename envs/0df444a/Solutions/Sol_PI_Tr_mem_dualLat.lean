-- Prove2me | solution 1 for PI.Tr.mem_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:55.647878+00:00
-- url     : https://prove2.me/submissions/1c02808d-c86b-44ba-968d-c0d0a8924dea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped Real
noncomputable section
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Λ : Submodule ℤ E}
    {y : E} : y ∈ dualLat Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ) := Iff.rfl
end PI.Tr
