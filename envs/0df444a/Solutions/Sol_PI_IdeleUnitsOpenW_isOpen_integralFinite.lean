-- Prove2me | solution 1 for PI.IdeleUnitsOpenW.isOpen_integralFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:21.867622+00:00
-- url     : https://prove2.me/submissions/e37762c4-00b6-4176-af5b-1100bbf81335

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers
import Theorems.Thm_PI_IdeleUnitsOpenW_isOpen_adicCompletionIntegers

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
theorem _root_.solution :
    IsOpen {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L} :=
  RestrictedProduct.isOpen_forall_mem (isOpen_adicCompletionIntegers L)
end PI.IdeleUnitsOpenW
