-- Prove2me | solution 1 for WeierstrassCurve.variableChange_mk_neg_one_smul_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e68a0f43-1950-58ec-86de-31428a1bc741

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self

set_option autoImplicit false

open WeierstrassCurve

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange R) • W = W := by
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_neg_one, inv_one, Units.val_neg, Units.val_one] <;> ring

end S_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self
end P2MW
export P2MW.S_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self (solution)
