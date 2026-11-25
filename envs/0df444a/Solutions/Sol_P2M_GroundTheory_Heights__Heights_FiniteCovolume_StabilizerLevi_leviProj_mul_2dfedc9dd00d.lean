-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_mul_2dfedc9dd00d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:36.868806+00:00
-- url     : https://prove2.me/submissions/7998b72a-945e-4275-84fa-89ff40646406

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07
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
theorem _root_.solution {g g' : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hgX : g *ᵥ X = X)
    (hg' : g'ᴴ * H * g' = H) (hgX' : g' *ᵥ X = X) :
    leviProj H B (g * g') = leviProj H B g * leviProj H B g' := by
  rw [ext_iff_mulVec]
  intro c
  have hAX := leftInv_mulVec_eq_zero hBX
  have e := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g' *ᵥ (B *ᵥ c))
    (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg' hgX' c)
  simp only [leviProj, ← mulVec_mulVec]
  rw [e, mulVec_sub, mulVec_smul, hgX, mulVec_sub, mulVec_smul, hAX, smul_zero, sub_zero]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
