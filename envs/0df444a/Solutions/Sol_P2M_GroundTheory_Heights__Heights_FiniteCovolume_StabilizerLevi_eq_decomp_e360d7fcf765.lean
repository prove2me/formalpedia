-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_decomp_e360d7fcf765
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:52.915685+00:00
-- url     : https://prove2.me/submissions/9844cd1a-b239-455a-a432-78c63301ed21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_swap_b2eefeb2a9e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_24167f725f84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {X Y : ι → ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
    (z : ι → ℂ) :
    z = (star Y ⬝ᵥ (H *ᵥ z)) • X + (star X ⬝ᵥ (H *ᵥ z)) • Y + B *ᵥ (leftInv H B *ᵥ z) := by
  obtain ⟨a, b, c, rfl⟩ := hspan z
  have hYX : star Y ⬝ᵥ (H *ᵥ X) = 1 := by rw [ip_swap hH, hXY, star_one]
  have hAX := leftInv_mulVec_eq_zero hBX
  have hAY := leftInv_mulVec_eq_zero hBY
  have h2 := leftInv_mul hG (H := H) (B := B)
  simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hYX, hYY, hXX,
    hXY, ip_B_right hH hBX, ip_B_right hH hBY, hAX, hAY, smul_zero, zero_add, mul_one, mul_zero,
    add_zero]
  rw [show leftInv H B *ᵥ (B *ᵥ c) = c by rw [mulVec_mulVec, h2, one_mulVec]]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
