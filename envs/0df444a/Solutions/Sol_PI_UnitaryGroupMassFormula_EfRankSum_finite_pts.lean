-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.finite_pts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:05.378737+00:00
-- url     : https://prove2.me/submissions/c2bcaf44-3237-41b2-bd21-c3674ad8a0e2

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
namespace PI.UnitaryGroupMassFormula.EfRankSum
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] : Finite (Pts O A) := by
  classical
  haveI : Finite ((maximalIdeal O).primesOver ↥(As O A)) := by
    have hfin : ((maximalIdeal O).primesOver ↥(As O A)).Finite :=
      Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)
    exact hfin.to_subtype
  exact Finite.of_equiv _ (ptsEquiv O A).symm
end PI.UnitaryGroupMassFormula.EfRankSum
