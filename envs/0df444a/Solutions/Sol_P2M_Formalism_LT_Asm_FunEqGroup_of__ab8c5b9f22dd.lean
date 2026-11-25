-- Prove2me | solution 1 for P2M_Formalism_LT_Asm_FunEqGroup_of__ab8c5b9f22dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:53:02.499843+00:00
-- url     : https://prove2.me/submissions/25331396-c868-482d-bc91-a5bd9aa4064a

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Theorems.Thm_Formalism_LT_Asm_integralMv_X
import Theorems.Thm_Formalism_LT_Asm_funEqMv_add
import Theorems.Thm_Formalism_LT_Asm_funEqInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.Asm
open Formalism.G
namespace Formalism.LT.Asm
theorem _root_.solution (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfE
  have hq := q_ne_zero hS
  have hG0 : MvPowerSeries.constantCoeff (atX f + atY f) = 0 := by
    rw [map_add, atX, atY, PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0,
      PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0, add_zero]
  have hGE : IsFunEqTypeMv p q hq σ (atX f + atY f) :=
    funEqMv_add hq σ (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 0))
      (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 1))
  obtain ⟨F, hF0, hF⟩ := h1 K (Fin 2) f (atX f + atY f) hf0 hf1 hG0
  refine ⟨F, hF0, funEqInv h2 h3 hk hS hf0 hf1 hfE F hF0 ?_, hF⟩
  rw [hF]
  exact hGE
end Formalism.LT.Asm
