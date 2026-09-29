-- Prove2me | solution 1 for PeriodPair.exists_variableChange_smul_weierstrassCurve_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cd5d01de-195f-57c3-8d1a-160c9b151e8c

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_jLattice_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq

set_option autoImplicit false

theorem solution (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • L.weierstrassCurve = E := by
  obtain ⟨L, hΔ, hj⟩ := PeriodPair.jLattice_surjective E.j
  haveI : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ.weierstrassCurve_Δ_ne_zero⟩
  have hjE : L.weierstrassCurve.j = E.j := by
    rw [← hj, L.jLattice_eq_c₄_pow_three_div_Δ, WeierstrassCurve.j, div_eq_mul_inv, mul_comm,
      Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  exact ⟨L, WeierstrassCurve.exists_variableChange_of_j_eq L.weierstrassCurve E hjE⟩

end S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
end P2MW
export P2MW.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq (solution)
