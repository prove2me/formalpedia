-- Prove2me | solution 1 for P2M_GlobalTheory_FormalCalc_subst_neg__a159bda6c5e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:51.07096+00:00
-- url     : https://prove2.me/submissions/5360f847-d4be-4e2a-ba9d-dd3f11178522

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
theorem _root_.solution {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (-f) = -subst a f := by
  rw [← substAlgHom_apply ha, map_neg, substAlgHom_apply]
end GlobalTheory.FormalCalc
