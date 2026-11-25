-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.finrank_as
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:41.738784+00:00
-- url     : https://prove2.me/submissions/67598a7f-7be3-4785-9803-7b0af5103912

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_free_as
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_isLocalizedModule_as

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
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    [Module.Finite O ↥(As O A)] : Module.finrank O ↥(As O A) = Module.finrank K A := by
  haveI : Module.Free O ↥(As O A) := free_as O K A
  haveI := isLocalizedModule_as O K A
  let b := Module.Free.chooseBasis O ↥(As O A)
  let b' := b.ofIsLocalizedModule K (nonZeroDivisors O) ((As O A).val.toLinearMap)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']
end PI.UnitaryGroupMassFormula.EfRankSum
