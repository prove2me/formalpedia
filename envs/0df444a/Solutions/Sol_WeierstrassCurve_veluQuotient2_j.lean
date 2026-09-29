-- Prove2me | solution 1 for WeierstrassCurve.veluQuotient2_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f14c3731-d5ff-5eb0-9b22-c2161af724b3

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluQuotientJInvariant
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_eq
import Theorems.Thm_WeierstrassCurve_veluQuotient2_cFour
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluQuotient2_j

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic] {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic :=
      isElliptic_veluQuotient2_of_isElliptic hQ hgy
    (W.veluQuotient2 x₀ y₀).j
      = (W.c₄ + 240 * W.veluGx x₀ y₀) ^ 3
        / (W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2) := by
  haveI hE : (W.veluQuotient2 x₀ y₀).IsElliptic :=
    isElliptic_veluQuotient2_of_isElliptic hQ hgy
  have hΔ' : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := (W.veluQuotient2 x₀ y₀).isUnit_Δ.ne_zero
  rw [← veluQuotient2_Delta_eq hQ hgy, eq_div_iff hΔ', mul_comm, Δ_mul_j, veluQuotient2_cFour]

end S_WeierstrassCurve_veluQuotient2_j
end P2MW
export P2MW.S_WeierstrassCurve_veluQuotient2_j (solution)
