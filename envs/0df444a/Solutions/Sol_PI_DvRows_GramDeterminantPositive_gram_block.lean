-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.gram_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:54.76273+00:00
-- url     : https://prove2.me/submissions/78ade06f-80a5-4bf2-a395-7d40f60596aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution {k d : Type*} [Fintype k] [DecidableEq k] [Fintype d] [DecidableEq d]
    (Uc : Matrix m k ℂ) (Zc Ac : Matrix m d ℂ) (T : Matrix (k ⊕ d) d ℂ)
    (hT : Ac = fromCols Uc Zc * T) (hAU : Acᴴ * Uc = 0) (hg : (Ucᴴ * Uc).det ≠ 0) :
    (Ucᴴ * Uc).det * ((Acᴴ * Zc).det * star (Acᴴ * Zc).det) =
      (Acᴴ * Ac).det * ((fromCols Uc Zc)ᴴ * fromCols Uc Zc).det := by
  set B := fromCols Uc Zc with hBdef
  set Rm : Matrix (k ⊕ d) (k ⊕ d) ℂ := fromBlocks 1 T.toRows₁ 0 T.toRows₂ with hRm
  have hBR : B * Rm = fromCols Uc Ac := by
    rw [hBdef, hRm, fromCols_mul_fromBlocks, hT, ← fromRows_toRows T, fromCols_mul_fromRows]
    simp
  have e1 : (fromCols Uc Ac)ᴴ * B = fromBlocks (Ucᴴ * Uc) (Ucᴴ * Zc) 0 (Acᴴ * Zc) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, hBdef, fromRows_mul_fromCols, hAU]
  have e2 : (fromCols Uc Ac)ᴴ * fromCols Uc Ac =
      fromBlocks (Ucᴴ * Uc) (Ucᴴ * Ac) 0 (Acᴴ * Ac) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, hAU]
  have f1 : (Ucᴴ * Uc).det * (Acᴴ * Zc).det = star Rm.det * (Bᴴ * B).det := by
    rw [← det_fromBlocks_zero₂₁ (Ucᴴ * Uc) (Ucᴴ * Zc) (Acᴴ * Zc), ← e1, ← hBR]
    have : (B * Rm)ᴴ * B = Rmᴴ * (Bᴴ * B) := by rw [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, det_mul, det_conjTranspose]
  have f2 : (Ucᴴ * Uc).det * (Acᴴ * Ac).det = star Rm.det * (Bᴴ * B).det * Rm.det := by
    rw [← det_fromBlocks_zero₂₁ (Ucᴴ * Uc) (Ucᴴ * Ac) (Acᴴ * Ac), ← e2, ← hBR]
    have : (B * Rm)ᴴ * (B * Rm) = Rmᴴ * (Bᴴ * B) * Rm := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, det_mul, det_mul, det_conjTranspose]
  have hgs : star (Ucᴴ * Uc).det = (Ucᴴ * Uc).det := by
    rw [← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have hGs : star (Bᴴ * B).det = (Bᴴ * B).det := by
    rw [← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  set g := (Ucᴴ * Uc).det
  set p := (Acᴴ * Zc).det
  set a := (Acᴴ * Ac).det
  set G := (Bᴴ * B).det
  set r := Rm.det
  have h3 : g * star p = r * G := by
    have := congrArg star f1
    rw [star_mul', star_mul', hgs, hGs, star_star] at this
    linear_combination this
  apply mul_left_cancel₀ hg
  linear_combination (g * star p) * f1 + (star r * G) * h3 - G * f2
end PI.DvRows.GramDeterminantPositive
