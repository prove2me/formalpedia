-- Prove2me | solution 1 for WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d25b1575-7b58-5c60-85a8-a482b95a4530

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq

open Polynomial

theorem PortCard.natDegree_Φ_sub_C_mul_ΨSq {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) (n : ℤ) (c : R) :
    (W.Φ n - C c * W.ΨSq n).natDegree = n.natAbs ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [WeierstrassCurve.Φ_zero, WeierstrassCurve.ΨSq_zero, mul_zero, sub_zero, natDegree_one,
      Int.natAbs_zero, zero_pow two_ne_zero]
  · have h1 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)
    rw [natDegree_sub_eq_left_of_natDegree_lt, WeierstrassCurve.natDegree_Φ]
    calc (C c * W.ΨSq n).natDegree ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
      _ ≤ n.natAbs ^ 2 - 1 := WeierstrassCurve.natDegree_ΨSq_le W n
      _ < n.natAbs ^ 2 := Nat.sub_lt (by omega) one_pos
      _ = (W.Φ n).natDegree := (WeierstrassCurve.natDegree_Φ W n).symm

theorem solution {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) (n : ℤ) (c : R) : (W.Φ n - Polynomial.C c * W.ΨSq n).natDegree = n.natAbs ^ 2 :=
  PortCard.natDegree_Φ_sub_C_mul_ΨSq W n c

end S_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq
end P2MW
export P2MW.S_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq (solution)
