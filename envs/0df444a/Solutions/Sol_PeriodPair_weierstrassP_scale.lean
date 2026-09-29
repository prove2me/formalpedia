-- Prove2me | solution 1 for PeriodPair.weierstrassP_scale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cc8c2bc0-6ca8-57e3-9feb-7d9dfc93fe28

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_weierstrassP_scale

set_option autoImplicit false

noncomputable section

open PeriodPair

theorem solution (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    (L.scale α).weierstrassP ((α : ℂ) * z) = ((α : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP,
    ← (L.scale α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (α : ℂ) * z - ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) =
      α * (z - (p.1 * L.ω₁ + p.2 * L.ω₂)) by ring,
    show ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) = α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_pow, one_div, one_div, one_div, one_div, mul_inv, mul_inv, mul_sub]

end
end S_PeriodPair_weierstrassP_scale
end P2MW
export P2MW.S_PeriodPair_weierstrassP_scale (solution)
