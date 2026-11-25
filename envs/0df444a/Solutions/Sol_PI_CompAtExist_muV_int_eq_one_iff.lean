-- Prove2me | solution 1 for PI.CompAtExist.muV_int_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:42.072678+00:00
-- url     : https://prove2.me/submissions/3e817ca5-a875-436b-8d5d-9d26fc44b6b8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
import Theorems.Thm_PI_CompAtExist_muV_int_le_one
import Theorems.Thm_PI_CompAtExist_muV_int_lt_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
namespace PI.CompAtExist
theorem _root_.solution (s : SplitPlace L) (r : 𝓞 L) :
    muV s (algebraMap (𝓞 L) L r) = 1 ↔ r ∉ s.w.asIdeal := by
  rw [← muV_int_lt_one_iff, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (muV_int_le_one s r) h⟩
end PI.CompAtExist
