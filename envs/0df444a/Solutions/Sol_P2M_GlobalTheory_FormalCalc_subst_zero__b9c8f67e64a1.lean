-- Prove2me | solution 1 for P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:50.860821+00:00
-- url     : https://prove2.me/submissions/cf7efaaa-4ba5-453c-b72d-fbdf7dc45030

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
    subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← substAlgHom_apply ha, map_zero]
end GlobalTheory.FormalCalc
