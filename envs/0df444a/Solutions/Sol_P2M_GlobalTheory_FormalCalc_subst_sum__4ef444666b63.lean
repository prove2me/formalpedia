-- Prove2me | solution 1 for P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:34.752023+00:00
-- url     : https://prove2.me/submissions/fc89e638-c35c-46de-97b1-d5a4f5d51f0e

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
theorem _root_.solution {κ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (s : Finset κ)
    (f : κ → MvPowerSeries σ R) : subst a (∑ k ∈ s, f k) = ∑ k ∈ s, subst a (f k) := by
  rw [← substAlgHom_apply ha, map_sum]
  simp only [substAlgHom_apply]
end GlobalTheory.FormalCalc
