-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_eq_one_iff_7ac75035cbda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:18.21857+00:00
-- url     : https://prove2.me/submissions/b90e1835-0696-462a-a380-818b14d8d533

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_24167f725f84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_mulVec_leftInv_of_8284feb2c2cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_X_unitary_B_765f6371e569

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
theorem _root_.solution {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X) :
    leviProj H B g = 1 ↔
      ∀ z : ι → ℂ, star X ⬝ᵥ (H *ᵥ z) = 0 → ∃ c : ℂ, g *ᵥ z = z + c • X := by
  have hAX := leftInv_mulVec_eq_zero hBX
  constructor
  · intro h1 z hz
    set u := leftInv H B *ᵥ z with hu
    have e1 : z = (star Y ⬝ᵥ (H *ᵥ z)) • X + B *ᵥ u := by
      rw [hu, mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan z hz]
      abel
    have e2 := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g *ᵥ (B *ᵥ u))
      (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX u)
    have e3 : leftInv H B *ᵥ (g *ᵥ (B *ᵥ u)) = u := by
      rw [mulVec_mulVec, mulVec_mulVec]
      change leviProj H B g *ᵥ u = u
      rw [h1, one_mulVec]
    rw [e3, eq_sub_iff_add_eq] at e2
    refine ⟨star Y ⬝ᵥ (H *ᵥ (g *ᵥ (B *ᵥ u))), ?_⟩
    conv_lhs => rw [e1]
    rw [mulVec_add, mulVec_smul, hgX]
    conv_rhs => rw [e1]
    rw [add_assoc, e2]
  · intro h1
    rw [ext_iff_mulVec]
    intro d
    obtain ⟨c, hc⟩ := h1 (B *ᵥ d) (ip_B_right hH hBX d)
    simp only [leviProj, ← mulVec_mulVec]
    rw [hc, mulVec_add, mulVec_smul, hAX, smul_zero, add_zero, mulVec_mulVec, leftInv_mul hG,
      one_mulVec]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
