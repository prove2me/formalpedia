-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.we
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:20:13.516801+00:00
-- url     : https://prove2.me/submissions/50352f5f-16f4-4871-baea-68176468b0db

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
theorem _root_.solution (c : Fin k) (a : Fin r) : hJ ε (L.w c) (L.e a) = 0 := by
  rw [hJ_conj, L.ew, star_zero]
end PI.ScPiBuildW.Loc.LocFrame
