-- Prove2me | solution 1 for P2M_Formalism_LT_Asm_FunEqHom_of__1ee5dca2153b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:53:04.378825+00:00
-- url     : https://prove2.me/submissions/080f04f5-9b14-4e3e-a5ea-8b3bbed34274

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Theorems.Thm_Formalism_LT_Asm_funEqInv
import Theorems.Thm_Formalism_LT_Asm_funEqType_unit

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
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} := by
  intro K _ _ _ p q σ hS f g hf0 hf1 hfE hg0 hgE
  obtain ⟨h, hh0, hh⟩ := h1 K Unit f (g : MvPowerSeries Unit K) hf0 hf1 hg0
  have hI : IntegralMv h := funEqInv h2 h3 hk hS hf0 hf1 hfE h hh0 (by
    rw [hh]
    exact funEqType_unit (q_ne_zero hS) hgE)
  exact ⟨h, hh0, fun n => hI _, hh⟩
end Formalism.LT.Asm
