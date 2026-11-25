-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_unitary_03bc851e798c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:28:28.338398+00:00
-- url     : https://prove2.me/submissions/02f792db-0cfb-4157-adcd-1d1a6bf2dbbc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_sesq_mul_064c0e5bfacf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ext_sesq_f168d8060b14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_unitary_881309351cf8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_left_c137c8023bfd
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
    (leviProj H B g)ᴴ * (Bᴴ * H * B) * leviProj H B g = Bᴴ * H * B := by
  apply ext_sesq
  intro c d
  have ec := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g *ᵥ (B *ᵥ c))
    (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX c)
  have ed := mulVec_leftInv_of hH hG hBX hBY hXX hYY hXY hspan (g *ᵥ (B *ᵥ d))
    (ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX d)
  have h1 : star (g *ᵥ (B *ᵥ c)) ⬝ᵥ (H *ᵥ X) = 0 := by
    conv_lhs => rw [← hgX]
    rw [ip_unitary hg, ip_B_left hBX]
  have h2 := ip_X_unitary_B hH hG hBX hBY hXX hYY hXY hspan hg hgX d
  rw [sesq_mul, sesq_mul, sesq_mul]
  simp only [leviProj, ← mulVec_mulVec]
  rw [ec, ed]
  simp only [star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, h1, h2, hXX, smul_zero, sub_zero, smul_eq_mul]
  rw [ip_unitary hg]
  simp only [mul_zero, sub_zero]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
