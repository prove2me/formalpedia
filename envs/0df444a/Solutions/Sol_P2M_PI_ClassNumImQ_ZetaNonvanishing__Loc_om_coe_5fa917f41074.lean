-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__Loc_om_coe_5fa917f41074
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:05.897607+00:00
-- url     : https://prove2.me/submissions/54260608-e49c-4591-bf98-8c171c06203d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ClassNumImQInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticInvariants_QuadPolyIrreducible
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_LocOdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂ PI.ClassNumImQ.ZetaNonvanishing₂.Loc
variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}
namespace PI.ClassNumImQ.ZetaNonvanishing₂.Loc
theorem _root_.solution (hq : QuadData d K b) : ((om hq : 𝓞 K) : K) = (1 + b) / 2 := rfl
end PI.ClassNumImQ.ZetaNonvanishing₂.Loc
