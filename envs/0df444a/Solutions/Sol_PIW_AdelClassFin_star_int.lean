-- Prove2me | solution 1 for PIW.AdelClassFin.star_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:35.501455+00:00
-- url     : https://prove2.me/submissions/42e4a050-bac5-47e0-9cb7-77cba466b0d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
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
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
namespace PIW.AdelClassFin
theorem _root_.solution {E : Type} [Field E] [NumberField E] [StarRing E] (q : 𝓞 E) :
    ∃ q' : 𝓞 E, algebraMap (𝓞 E) E q' = star (algebraMap (𝓞 E) E q) := by
  have h : IsIntegral ℤ (algebraMap (𝓞 E) E q) := by
    first
      | exact NumberField.RingOfIntegers.isIntegral_coe q
      | exact q.2
  have h2 : IsIntegral ℤ (star (algebraMap (𝓞 E) E q)) := by
    have h3 := h.map (starRingEnd E).toIntAlgHom
    first
      | exact h3
      | simpa using h3
  exact ⟨⟨_, h2⟩, rfl⟩
end PIW.AdelClassFin
