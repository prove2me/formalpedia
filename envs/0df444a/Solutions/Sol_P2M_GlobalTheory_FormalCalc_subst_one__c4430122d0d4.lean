-- Prove2me | solution 1 for P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:52.27815+00:00
-- url     : https://prove2.me/submissions/8cba5026-1694-4d20-b743-3414dd9b3bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← substAlgHom_apply ha, map_one]
end GlobalTheory.FormalCalc
