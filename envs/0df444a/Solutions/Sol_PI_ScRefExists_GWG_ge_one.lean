-- Prove2me | solution 1 for PI.ScRefExists.GWG.ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:54.757321+00:00
-- url     : https://prove2.me/submissions/f494db63-45c0-4f9a-bff6-a5656b5a2a1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GWG
theorem _root_.solution {x : I.E} (hx : x ∈ (algebraMap (𝓞 I.E) I.E).range) : GE I 1 x := by
  obtain ⟨s, rfl⟩ := hx
  exact ⟨s, by rw [Nat.cast_one, one_mul]⟩
end PI.ScRefExists.GWG
