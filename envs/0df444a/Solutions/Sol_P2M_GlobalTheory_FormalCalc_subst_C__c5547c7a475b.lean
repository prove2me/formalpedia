-- Prove2me | solution 1 for P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:52.282139+00:00
-- url     : https://prove2.me/submissions/d4520404-4d1f-454c-8ef5-c6d63d2dd819

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
theorem _root_.solution {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (r : R) :
    subst a (C r : MvPowerSeries σ R) = C (algebraMap R S r) := by
  rw [← substAlgHom_apply ha, show (C r : MvPowerSeries σ R) = algebraMap R _ r from rfl,
    AlgHom.commutes, MvPowerSeries.algebraMap_apply]
end GlobalTheory.FormalCalc
