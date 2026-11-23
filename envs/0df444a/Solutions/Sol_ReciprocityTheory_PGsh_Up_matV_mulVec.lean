-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.matV_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:09.912485+00:00
-- url     : https://prove2.me/submissions/0a830409-aa57-4fd8-b958-94d116159cb6

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
theorem _root_.solution (w : Fin g → R) :
    matV P φ *ᵥ w = φ ⟨P *ᵥ w, ⟨_, rfl⟩⟩ := by
  have hw : (⟨P *ᵥ w, ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) =
      ∑ k, w k • (⟨P *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_lhs => rw [sum_single' w]
    rw [show P *ᵥ (∑ k, w k • (Pi.single k 1 : Fin g → R)) =
        Matrix.mulVecLin P (∑ k, w k • (Pi.single k 1 : Fin g → R)) from rfl, map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply]
  rw [hw, map_sum]
  simp only [LinearEquiv.map_smul]
  funext l
  simp only [Matrix.mulVec, dotProduct, matV, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end ReciprocityTheory.PGsh.Up
