-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_range_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:02.442144+00:00
-- url     : https://prove2.me/submissions/54af54ae-ff23-48e3-a365-2f9b2c93ecfd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution :
    ∀ (o : 𝓞 E) (s : E), s ∈ Set.range ((↑) : 𝓞 E → E) → (o : E) * s ∈ Set.range ((↑) : 𝓞 E → E) := by
  rintro o _ ⟨t, rfl⟩
  exact ⟨o * t, by push_cast; rfl⟩
end PI.LocFramePrimWork
