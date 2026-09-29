-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.finrank_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/44ccdbed-3134-5ede-bca2-b8be773c8caa

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four

set_option autoImplicit false

open scoped Quaternion

theorem solution {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩
  have hr : Module.rank ℤ Λ = Module.rank ℚ ℍ[ℚ, a, b] := Submodule.IsLattice.rank' ℚ Λ
  rw [QuaternionAlgebra.rank_eq_four] at hr
  exact Module.finrank_eq_of_rank_eq hr

end S_QuaternionAlgebra_IsOrder_finrank_eq_four
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four (solution)
