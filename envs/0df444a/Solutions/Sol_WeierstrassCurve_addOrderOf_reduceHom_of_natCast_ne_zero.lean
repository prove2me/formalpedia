-- Prove2me | solution 1 for WeierstrassCurve.addOrderOf_reduceHom_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ee34f630-b3fe-54fd-a35b-2fb97de2d660

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : addOrderOf P = N) :
    addOrderOf (reduceHom hΔ P) = N := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul, ← hP, addOrderOf_nsmul_eq_zero, map_zero]
  · rw [← hP]
    apply addOrderOf_dvd_of_nsmul_eq_zero
    refine WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero hΔ hN ?_ (smul_zero _) ?_
    · rw [smul_comm, ← hP, addOrderOf_nsmul_eq_zero, smul_zero]
    · rw [map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]

end S_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero (solution)
