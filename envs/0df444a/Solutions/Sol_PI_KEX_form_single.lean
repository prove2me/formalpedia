-- Prove2me | solution 1 for PI.KEX.form_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:27.21834+00:00
-- url     : https://prove2.me/submissions/a616a651-e79e-40c4-b679-39361104a59c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KoszulExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KoszulImageInIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KernelExtensionOfKoszulLoweringImageLeviWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PI PI.KEX
open PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}
namespace PI.KEX
theorem _root_.solution (s : Fin D → R) (k : Fin D) : form s (Pi.single k 1) = s k := by
  simp [form, Pi.single_apply]
end PI.KEX
