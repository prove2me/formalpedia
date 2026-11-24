-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSelfDual.int_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:18.791233+00:00
-- url     : https://prove2.me/submissions/f5a037fc-2132-4119-bd23-aba37fca09a2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualDifferent_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSelfDual
namespace PI.UnitaryGroupMassFormula.KerSelfDual
theorem _root_.solution {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E) (x : 𝓞 E) :
    ∃ x' : 𝓞 E, algebraMap (𝓞 E) E x' = cj (algebraMap (𝓞 E) E x) := by
  have h : IsIntegral ℤ (algebraMap (𝓞 E) E x) := (IsIntegralClosure.isIntegral ℤ E x).algebraMap
  have h' : IsIntegral ℤ (cj (algebraMap (𝓞 E) E x)) :=
    IsIntegral.map ((cj : E →+* E).toIntAlgHom) h
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp h'
end PI.UnitaryGroupMassFormula.KerSelfDual
