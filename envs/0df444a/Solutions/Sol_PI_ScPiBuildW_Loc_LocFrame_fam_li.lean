-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.fam_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:04.71923+00:00
-- url     : https://prove2.me/submissions/2f70b2fa-9b9b-4eda-8f3f-2913bc141d0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_zero_right
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_fe
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_we
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_wf
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_wz
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_ze
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_zf
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_pair
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
theorem _root_.solution : LinearIndependent ℂ L.fam := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ x, (∑ a, g (.inl (.inl a)) * hJ ε x (L.e a)) + (∑ a, g (.inl (.inr a)) * hJ ε x (L.f a)) +
      (g (.inr (.inl ())) * hJ ε x L.z + ∑ c, g (.inr (.inr c)) * hJ ε x (L.w c)) = 0 := fun x => by
    rw [← L.pair x g, hg, hJ_zero_right]
  have hf : ∀ b, g (.inl (.inr b)) = 0 := fun b => by
    have := key (L.e b)
    simpa [L.ee, L.ef, L.ez, L.ew] using this
  have hz : g (.inr (.inl ())) = 0 := by
    have := key L.z
    have h2 : g (.inr (.inl ())) * hJ ε L.z L.z = 0 := by simpa [L.ze, L.zf, L.zw] using this
    exact (mul_eq_zero.mp h2).resolve_right L.zz
  have hw : ∀ c, g (.inr (.inr c)) = 0 := fun c => by
    have := key (L.w c)
    simpa [L.we, L.wf, L.wz, L.ww] using this
  have he : ∀ b, g (.inl (.inl b)) = 0 := fun b => by
    have := key (L.f b)
    simpa [L.fe, hf, hz, hw] using this
  rintro ((a | a) | (⟨⟩ | c))
  · exact he a
  · exact hf a
  · exact hz
  · exact hw c
end PI.ScPiBuildW.Loc.LocFrame
