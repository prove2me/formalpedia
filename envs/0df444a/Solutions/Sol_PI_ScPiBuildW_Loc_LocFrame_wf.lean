-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.wf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:20:14.343146+00:00
-- url     : https://prove2.me/submissions/a4267905-2572-4c23-9114-85e516e41fb5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_conj

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
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution (c : Fin k) (a : Fin r) : hJ ε (L.w c) (L.f a) = 0 := by
  rw [hJ_conj, L.fw, star_zero]
end PI.ScPiBuildW.Loc.LocFrame
