-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.detGram_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:56.5337+00:00
-- url     : https://prove2.me/submissions/58f485d7-f1c6-4ac3-9354-2a8895219487

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_cellMat_eq
import Theorems.Thm_ReciprocityTheory_AnForm_P_eval_cpP
import Theorems.Thm_ReciprocityTheory_AnForm_P_zMat_real_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
open Matrix Polynomial
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (s : ℝ) :
    detGram N hd m hm (s • v) = ((Gm N hd m hm v).det.eval (s : ℂ)).re := by
  have h1 : cellMat N (s • v) =
      ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • zMat N v ^ k := by
    rw [cellMat_eq, zMat_real_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.smul_pow, smul_smul, mul_comm]
  have h2 : (cellMat N (s • v))ᴴ =
      ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • (zMat N v)ᴴ ^ k := by
    rw [h1, conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_smul, conjTranspose_pow]
    congr 1
    simp [Complex.conj_ofReal]
  have hG : (gP N hd v).map (eval (s : ℂ)) =
      (cellMat N (s • v))ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N (s • v) := by
    rw [gP, ← coe_evalRingHom, Matrix.map_mul, Matrix.map_mul, coe_evalRingHom, eval_cpP,
      eval_cpP, h2, h1, Matrix.mul_assoc]
    congr 2
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h]
  unfold detGram
  rw [← hG]
  congr 1
  rw [← coe_evalRingHom, RingHom.map_det]
  rfl
end ReciprocityTheory.AnForm.P
