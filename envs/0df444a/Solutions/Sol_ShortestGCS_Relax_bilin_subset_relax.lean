-- Prove2me | solution 1 for ShortestGCS.Relax.bilin_subset_relax
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:16:06.265225+00:00
-- url     : https://prove2.me/submissions/738dc9bc-86c0-4864-9770-c0acbbf8098e

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

open ShortestGCS.Relax Matrix

theorem solution {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ)) :
    bilinSet X Y ⊆ relaxSet X Y := by
  rintro ⟨x, y, Z⟩ ⟨hx, hy, hZ⟩
  change Z = vecMulVec x y at hZ
  subst Z
  intro ab hab cd hcd
  have hnonneg := mul_nonneg (hab x hx) (hcd y hy)
  change 0 ≤ ab.1 ⬝ᵥ (vecMulVec x y *ᵥ cd.1) + cd.2 * (ab.1 ⬝ᵥ x) +
    ab.2 * (cd.1 ⬝ᵥ y) + ab.2 * cd.2
  rw [vecMulVec_mulVec, dotProduct_smul, dotProduct_comm y cd.1]
  simp only [op_smul_eq_mul]
  nlinarith only [hnonneg]

#print axioms solution
