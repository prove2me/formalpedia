-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:19.646455+00:00
-- url     : https://prove2.me/submissions/f6eae329-f52c-4fc7-b604-0e52acf002aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_sub_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_sum_right
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_fe
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_we
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_ze
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_orth_zero
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
theorem _root_.solution (y : Fin n → ℂ) (he : ∀ a, hJ ε (L.e a) y = 0) (hz : hJ ε L.z y = 0) :
    y = ∑ c, hJ ε (L.w c) y • L.w c + ∑ a, hJ ε (L.f a) y • L.e a := by
  suffices h : y - (∑ c, hJ ε (L.w c) y • L.w c + ∑ a, hJ ε (L.f a) y • L.e a) = 0 from
    sub_eq_zero.mp h
  apply L.orth_zero
  · intro b
    rw [hJ_sub_right, he b, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.ew, L.ee]
  · intro b
    rw [hJ_sub_right, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.fw, L.fe]
  · rw [hJ_sub_right, hz, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.zw, L.ze]
  · intro d
    rw [hJ_sub_right, hJ_add_right, hJ_sum_right, hJ_sum_right]
    simp [L.ww, L.we]
end PI.ScPiBuildW.Loc.LocFrame
