-- Prove2me | solution 1 for PI.LocLatEq.W.core_nontriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:13.678297+00:00
-- url     : https://prove2.me/submissions/e76a6e12-371e-46fc-bf97-c703e2690534

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe

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
theorem _root_.solution (A : LocAt F E sig p) : Nontrivial A.Ep := by
  by_contra h
  have : Subsingleton A.Ep := not_nontrivial_iff_subsingleton.1 h
  have h2 := A.rank
  rw [Module.finrank_zero_of_subsingleton] at h2
  omega
end PI.LocLatEq.W
