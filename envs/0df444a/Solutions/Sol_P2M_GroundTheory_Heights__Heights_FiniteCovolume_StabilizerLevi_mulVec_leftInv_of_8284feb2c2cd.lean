-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_mulVec_leftInv_of_8284feb2c2cd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:37.052876+00:00
-- url     : https://prove2.me/submissions/b41a1eda-53ce-46e1-af91-3bf7add680d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_eq_decomp_e360d7fcf765

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
variable (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
include hH hG hBX hBY hXX hYY hXY hspan
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution (z : ι → ℂ) (hz : star X ⬝ᵥ (H *ᵥ z) = 0) :
    B *ᵥ (leftInv H B *ᵥ z) = z - (star Y ⬝ᵥ (H *ᵥ z)) • X := by
  have := eq_decomp hH hG hBX hBY hXX hYY hXY hspan z
  rw [hz, zero_smul, add_zero] at this
  rw [eq_sub_iff_add_eq, add_comm]
  exact this.symm
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
