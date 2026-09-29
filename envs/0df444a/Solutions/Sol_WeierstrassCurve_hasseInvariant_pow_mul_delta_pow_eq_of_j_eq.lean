-- Prove2me | solution 1 for WeierstrassCurve.hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7b5d4d90-382c-5482-9411-a99b46f396de

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve

namespace P2mWs11W0

theorem hasseInvariant_pow_mul_Δ_pow_variableChange (q : ℕ) [Fact q.Prime]
    {R : Type*} [CommRing R] [CharP R q] (W : WeierstrassCurve R) (φ : VariableChange R) :
    hasseInvariant q (φ • W) ^ 12 * W.Δ ^ (q - 1) = hasseInvariant q W ^ 12 * (φ • W).Δ ^ (q - 1) := by
  rw [hasseInvariant_variableChange W φ, variableChange_Δ, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm 12 (q - 1)]
  ring

end P2mWs11W0

open ModularCurve in
theorem solution
    (q : ℕ) [Fact q.Prime]
    {F : Type*} [Field F] [CharP F q] [IsSepClosed F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (h : W.j = W'.j) :
    WeierstrassCurve.hasseInvariant q W ^ 12 * W'.Δ ^ (q - 1) =
      WeierstrassCurve.hasseInvariant q W' ^ 12 * W.Δ ^ (q - 1) := by
  obtain ⟨φ, rfl⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W W' h
  exact (P2mWs11W0.hasseInvariant_pow_mul_Δ_pow_variableChange q W φ).symm

end S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
end P2MW
export P2MW.S_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq (solution)
