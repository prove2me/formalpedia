-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:36.138128+00:00
-- url     : https://prove2.me/submissions/1e0e6841-e899-475a-bdc6-0d2196ba9a2d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_sum_right
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
theorem _root_.solution (x : Fin n → ℂ) (g : (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k) → ℂ) :
    hJ ε x (∑ i, g i • L.fam i) =
      (∑ a, g (.inl (.inl a)) * hJ ε x (L.e a)) + (∑ a, g (.inl (.inr a)) * hJ ε x (L.f a)) +
        (g (.inr (.inl ())) * hJ ε x L.z + ∑ c, g (.inr (.inr c)) * hJ ε x (L.w c)) := by
  rw [hJ_sum_right]
  simp only [Fintype.sum_sum_type, fam, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique]
  all_goals rfl
end PI.ScPiBuildW.Loc.LocFrame
