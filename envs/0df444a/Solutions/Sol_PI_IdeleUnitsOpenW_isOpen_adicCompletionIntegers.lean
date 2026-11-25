-- Prove2me | solution 1 for PI.IdeleUnitsOpenW.isOpen_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:15.327173+00:00
-- url     : https://prove2.me/submissions/f428d08b-f5b4-4177-ba81-9f54952cf829

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleUnitsOpen_IsOpenAdicCompletionIntegers

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) :
    IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := by
  have h : (v.adicCompletionIntegers L : Set (v.adicCompletion L)) =
      ((Valued.v : Valuation (v.adicCompletion L) _).integer : Set (v.adicCompletion L)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _
end PI.IdeleUnitsOpenW
