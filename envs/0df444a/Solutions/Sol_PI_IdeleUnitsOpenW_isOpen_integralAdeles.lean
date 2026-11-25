-- Prove2me | solution 1 for PI.IdeleUnitsOpenW.isOpen_integralAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:58:45.65404+00:00
-- url     : https://prove2.me/submissions/0acc4bed-e3b3-44bc-b4d4-f596c542e40e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers
import Theorems.Thm_PI_IdeleUnitsOpenW_isOpen_integralFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.IdeleUnitsOpenW
variable (L : Type) [Field L] [NumberField L]
namespace PI.IdeleUnitsOpenW
theorem _root_.solution : IsOpen (integralAdeles L) := by
  have h : integralAdeles L = Prod.snd ⁻¹'
      {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L} := by
    ext x
    exact Iff.rfl
  rw [h]
  exact (isOpen_integralFinite L).preimage continuous_snd
end PI.IdeleUnitsOpenW
