-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ASSmall.solPerf_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:20.102402+00:00
-- url     : https://prove2.me/submissions/ffedfdd1-3bca-4335-b69b-68d7311262d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_CoordPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ASSmall
variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
namespace PI.UnitaryGroupMassFormula.ASSmall
theorem _root_.solution (f : Perfection R p) {K : ℕ}
    (hK : Perfection.coeff R p 0 f ^ K = 0) :
    solPerf f hK ^ p - solPerf f hK = f := by
  ext m
  rw [map_sub, map_pow]
  change sol f K m ^ p - sol f K m = Perfection.coeff R p m f
  rw [sol, neg_sum_pow_p]
  simp_rw [← pow_mul, ← pow_succ]
  have e1 := Finset.sum_range_succ' (fun n => Perfection.coeff R p m f ^ p ^ n) (m + K)
  have e2 := Finset.sum_range_succ (fun n => Perfection.coeff R p m f ^ p ^ n) (m + K)
  have h0 := coord_pow_eq_zero f hK m (m + K) le_rfl
  simp only [pow_zero, pow_one] at e1
  linear_combination e1 - e2 - h0
end PI.UnitaryGroupMassFormula.ASSmall
