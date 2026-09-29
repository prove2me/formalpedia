-- Prove2me | solution 1 for QuaternionAlgebra.sq_sub_trd_mul_add_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/20f12f27-462d-56ea-91cf-ca0753e0fca7

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_sq_sub_trd_mul_add_nrd
open scoped Quaternion
open QuaternionAlgebra

theorem solution {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) :
    x * x - ((trd x : R) : ℍ[R, a, b]) * x + ((nrd x : R) : ℍ[R, a, b]) = 0 := by
  have h1 : ((trd x : R) : ℍ[R, a, b]) = x + star x := (add_star_eq_coe_trd x).symm
  have h2 : ((nrd x : R) : ℍ[R, a, b]) = star x * x := (star_mul_eq_coe_nrd x).symm
  rw [h1, h2, add_mul]
  abel

end S_QuaternionAlgebra_sq_sub_trd_mul_add_nrd
end P2MW
export P2MW.S_QuaternionAlgebra_sq_sub_trd_mul_add_nrd (solution)
