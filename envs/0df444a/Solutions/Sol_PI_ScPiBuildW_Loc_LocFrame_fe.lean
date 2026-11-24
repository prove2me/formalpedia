-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:15:15.617382+00:00
-- url     : https://prove2.me/submissions/7c2598a8-81a5-4e05-a5fa-e552b9937252

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_conj
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution (b a : Fin r) : hJ ε (L.f b) (L.e a) = if a = b then 1 else 0 := by
  rw [hJ_conj, L.ef]
  split_ifs <;> simp
end PI.ScPiBuildW.Loc.LocFrame
