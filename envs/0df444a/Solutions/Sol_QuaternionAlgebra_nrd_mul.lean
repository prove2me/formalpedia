-- Prove2me | solution 1 for QuaternionAlgebra.nrd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4a823d0c-96de-5680-82f3-83ae67103f18

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_nrd_mul
open scoped Quaternion
open QuaternionAlgebra

theorem solution {R : Type*} [CommRing R] {a b : R}
    (x y : ℍ[R, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [mk_mul_mk, nrd_mk]
  ring

end S_QuaternionAlgebra_nrd_mul
end P2MW
export P2MW.S_QuaternionAlgebra_nrd_mul (solution)
