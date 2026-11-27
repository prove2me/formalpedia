-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.hJ_nondeg_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:18:30.712871+00:00
-- url     : https://prove2.me/submissions/a9d0626e-86de-48c4-af77-89c449dffdeb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_conj
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_nondeg_right

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
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
variable {n : ℕ} (ε : Fin n → Bool)
namespace PI.ScPiBuildW.Loc
theorem _root_.solution (x : Fin n → ℂ) (h : ∀ y, hJ ε x y = 0) : x = 0 :=
  hJ_nondeg_right ε x fun y => by rw [hJ_conj, h y, star_zero]
end PI.ScPiBuildW.Loc
