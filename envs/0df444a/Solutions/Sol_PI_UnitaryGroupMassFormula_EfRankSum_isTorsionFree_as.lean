-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.isTorsionFree_as
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:25.468394+00:00
-- url     : https://prove2.me/submissions/76fc59eb-324c-4cb3-871f-e44b1377f526

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_isTorsionFree_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps
namespace PI.UnitaryGroupMassFormula.EfRankSum
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O ↥(As O A) := by
  obtain ⟨h⟩ := isTorsionFree_alg O K A
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • (a : A) = r • (b : A) := by
    have h2 := congrArg (fun x : ↥(As O A) => (x : A)) hab
    simpa using h2
  exact Subtype.ext (h hr hab')
end PI.UnitaryGroupMassFormula.EfRankSum
