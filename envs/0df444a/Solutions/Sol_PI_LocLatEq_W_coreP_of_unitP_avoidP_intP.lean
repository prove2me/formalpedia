-- Prove2me | solution 1 for PI.LocLatEq.W.coreP_of_unitP_avoidP_intP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:33.661848+00:00
-- url     : https://prove2.me/submissions/888a8dcf-894b-4f85-b4d9-f1f79a2281fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe
import Theorems.Thm_PI_LocLatEq_W_core_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.LocLatEq.W
theorem _root_.solution (hU : UnitP) (hA : AvoidP) (hI : IntP) : CoreP := by
  intro F E _ _ _ _ _ h2 sig p A n Λ hΛ y hy
  exact core_ind hU hA hI h2 A n Λ hΛ y hy
end PI.LocLatEq.W
