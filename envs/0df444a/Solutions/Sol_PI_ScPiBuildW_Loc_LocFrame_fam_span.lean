-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.fam_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:46.174425+00:00
-- url     : https://prove2.me/submissions/3c7dcbbe-8024-47a3-8a71-c81bae8967f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_fam_li
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
theorem _root_.solution : Submodule.span ℂ (Set.range L.fam) = ⊤ := by
  apply L.fam_li.span_eq_top_of_card_eq_finrank
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, Module.finrank_fin_fun]
  rw [L.hn]
  ring
end PI.ScPiBuildW.Loc.LocFrame
