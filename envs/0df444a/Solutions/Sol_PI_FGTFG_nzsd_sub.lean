-- Prove2me | solution 1 for PI.FGTFG.nzsd_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:26.663823+00:00
-- url     : https://prove2.me/submissions/219c3eec-e16f-459f-9731-23049addfa56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_FGTorsionFreeGenOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FGTFG
open Module
namespace PI.FGTFG
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (N : Submodule R M) : NoZeroSMulDivisors R N :=
  Function.Injective.noZeroSMulDivisors _ Subtype.val_injective rfl (fun _ _ => rfl)
end PI.FGTFG
