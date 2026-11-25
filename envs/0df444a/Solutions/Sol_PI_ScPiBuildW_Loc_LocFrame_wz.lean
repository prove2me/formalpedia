-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.wz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:54.487562+00:00
-- url     : https://prove2.me/submissions/c8504297-b92a-4ffe-8efc-047c03646ce2

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
theorem _root_.solution (c : Fin k) : hJ ε (L.w c) L.z = 0 := by
  rw [hJ_conj, L.zw, star_zero]
end PI.ScPiBuildW.Loc.LocFrame
