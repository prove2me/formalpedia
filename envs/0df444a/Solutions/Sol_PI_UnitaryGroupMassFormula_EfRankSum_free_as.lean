-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.free_as
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:35.038724+00:00
-- url     : https://prove2.me/submissions/1b4bee5e-a2e9-4d84-9617-aae267ac3f91

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_isTorsionFree_as

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
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A]
    [Module.Finite O ↥(As O A)] : Module.Free O ↥(As O A) := by
  haveI := isTorsionFree_as O K A
  exact Module.free_of_finite_type_torsion_free'
end PI.UnitaryGroupMassFormula.EfRankSum
