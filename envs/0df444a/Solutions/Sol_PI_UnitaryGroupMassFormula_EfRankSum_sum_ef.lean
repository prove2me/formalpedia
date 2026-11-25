-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.sum_ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:24.24775+00:00
-- url     : https://prove2.me/submissions/5fbfb529-a161-4c51-bdb0-38e6aff91fe6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Lattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_EfRankSumMain
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ep_eq_ramificationIdx
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_fdeg_eq_inertiaDeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_finite_pts
import Theorems.Thm_PI_UnitaryGroupMassFormula_EfRankSum_ptsEquiv_apply


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
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] [Module.Flat O ↥(As O A)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank O ↥(As O A) := by
  classical
  have : Finite (Pts O A) := finite_pts O A
  let : Fintype (Pts O A) := Fintype.ofFinite _
  let : Fintype ((maximalIdeal O).primesOver ↥(As O A)) := Fintype.ofEquiv _ (ptsEquiv O A)
  rw [finsum_eq_sum_of_fintype, ← Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal O),
    ← (ptsEquiv O A).sum_comp]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [ptsEquiv_apply, ep_eq_ramificationIdx hϖ, fdeg_eq_inertiaDeg]
end PI.UnitaryGroupMassFormula.EfRankSum
