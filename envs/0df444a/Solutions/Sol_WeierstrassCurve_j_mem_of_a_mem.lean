-- Prove2me | solution 1 for WeierstrassCurve.j_mem_of_a_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/27068548-cb19-503d-8ad1-c4be8770a508

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_j_mem_of_a_mem

set_option autoImplicit false

open WeierstrassCurve in
theorem solution {F : Type*} [Field F] {S : Type*} [SetLike S F] [SubfieldClass S F]
    (W : WeierstrassCurve F) [W.IsElliptic] (K : S)
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K) : W.j ∈ K := by
  have hb₂ : W.b₂ ∈ K := by
    rw [b₂]; exact add_mem (pow_mem h₁ 2) (mul_mem (ofNat_mem K 4) h₂)
  have hb₄ : W.b₄ ∈ K := by
    rw [b₄]; exact add_mem (mul_mem (ofNat_mem K 2) h₄) (mul_mem h₁ h₃)
  have hb₆ : W.b₆ ∈ K := by
    rw [b₆]; exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem K 4) h₆)
  have hb₈ : W.b₈ ∈ K := by
    rw [b₈]
    exact sub_mem (add_mem (sub_mem (add_mem (mul_mem (pow_mem h₁ 2) h₆)
      (mul_mem (mul_mem (ofNat_mem K 4) h₂) h₆)) (mul_mem (mul_mem h₁ h₃) h₄))
      (mul_mem h₂ (pow_mem h₃ 2))) (pow_mem h₄ 2)
  have hc₄ : W.c₄ ∈ K := by
    rw [c₄]; exact sub_mem (pow_mem hb₂ 2) (mul_mem (ofNat_mem K 24) hb₄)
  have hΔ : W.Δ ∈ K := by
    rw [Δ]
    exact add_mem (sub_mem (sub_mem (mul_mem (neg_mem (pow_mem hb₂ 2)) hb₈)
      (mul_mem (ofNat_mem K 8) (pow_mem hb₄ 3))) (mul_mem (ofNat_mem K 27) (pow_mem hb₆ 2)))
      (mul_mem (mul_mem (mul_mem (ofNat_mem K 9) hb₂) hb₄) hb₆)
  rw [WeierstrassCurve.j]
  refine mul_mem ?_ (pow_mem hc₄ 3)
  rw [Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  exact inv_mem hΔ

end S_WeierstrassCurve_j_mem_of_a_mem
end P2MW
export P2MW.S_WeierstrassCurve_j_mem_of_a_mem (solution)
