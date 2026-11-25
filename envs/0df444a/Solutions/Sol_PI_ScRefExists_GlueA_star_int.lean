-- Prove2me | solution 1 for PI.ScRefExists.GlueA.star_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:25:21.601799+00:00
-- url     : https://prove2.me/submissions/8b61a49f-f1a8-474b-8988-39f2bd46e6cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GlueA
theorem _root_.solution (t : 𝓞 I.E) : star (t : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have h : IsIntegral ℤ (star (t : I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe t).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨star (t : I.E), h⟩, rfl⟩
end PI.ScRefExists.GlueA
