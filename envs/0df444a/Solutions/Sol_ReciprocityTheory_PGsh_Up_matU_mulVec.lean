-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.matU_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:53.639569+00:00
-- url     : https://prove2.me/submissions/d9df2c56-6f47-4a0b-8f98-8e7759e4a6cc

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_DualLenStatement
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_sum_single__5b64b664eaa4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] {g d : ℕ} (P : Matrix (Fin g) (Fin g) R) (hP : P * P = P)
  (φ : LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R))
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (y : Fin d → R) : matU P φ *ᵥ y = (φ.symm y : Fin g → R) := by
  conv_rhs => rw [sum_single' y]
  rw [map_sum]
  funext k
  simp [matU, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
end ReciprocityTheory.PGsh.Up
