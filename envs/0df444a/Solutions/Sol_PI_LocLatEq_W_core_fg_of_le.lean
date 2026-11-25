-- Prove2me | solution 1 for PI.LocLatEq.W.core_fg_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:41.944797+00:00
-- url     : https://prove2.me/submissions/51519567-4dd5-4511-a008-8256a74f1f8e

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
namespace PI.LocLatEq.W
theorem _root_.solution {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M]
    [Module R M] {N P : Submodule R M} (hN : N.FG) (h : P ≤ N) : P.FG := by
  have : IsNoetherian R N := isNoetherian_of_fg_of_noetherian N hN
  have h1 : (P.comap N.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map N.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 h] at h2
end PI.LocLatEq.W
