-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sumLat_inv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:39.162399+00:00
-- url     : https://prove2.me/submissions/a75196fd-274b-42b7-989c-a9e9806a1d10

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
import Definitions.Def_ReciprocityTheory_DualLattices_SumLatInvMulVec
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


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
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (w : Fin n × Fin s → C)
    (τ : Fin n) (i : Fin s) :
    ((sumLat Mτ).B⁻¹ *ᵥ w) (τ, i) = ((Mτ τ).B⁻¹ *ᵥ fun j => w (τ, j)) i := by
  classical
  unfold sumLat
  simp only
  have hinv : (reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (blockDiagonal fun τ ↦ (Mτ τ).B))⁻¹ =
      reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
        (blockDiagonal fun τ ↦ (Mτ τ).B⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    have h1 : (fun τ ↦ (Mτ τ).B⁻¹ * (Mτ τ).B) = 1 :=
      funext fun τ ↦ Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (Mτ τ).det_ne)
    rw [h1, Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
  rw [hinv]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end ReciprocityTheory.PGsh.Up
