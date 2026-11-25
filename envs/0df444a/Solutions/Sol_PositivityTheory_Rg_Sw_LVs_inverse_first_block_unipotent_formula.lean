-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.inverse_first_block_unipotent_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:07.872163+00:00
-- url     : https://prove2.me/submissions/77b70aa7-c2bc-45f0-ac38-03f9236a525f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_InG
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inv_blocks_of_InG
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CmI_mul_Cm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_Cm_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Cm_mul_CmI
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_ub_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Lr_mX

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {x : M2 n} (hx : InG x) (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    ub1 (x * mX 1 Q R 1) = (u1 x)ᴴ + Q * (u2 x)ᴴ := by
  have hinv : (x * mX 1 Q R 1)⁻¹ = mX 1 (-Q) (-R) 1 * x⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    have hx1 : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x (isUnit_det_of_InG hx)
    have hfb : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-Q) (-R) 1 * Matrix.fromBlocks 1 Q R 1 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [hQR, hRQ]
    calc mX 1 (-Q) (-R) 1 * x⁻¹ * (x * mX 1 Q R 1) = mX 1 (-Q) (-R) 1 * (x⁻¹ * x) * mX 1 Q R 1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hx1, Matrix.mul_one, mX, mX, dp_Cm_inv]
          calc Cm n * Matrix.fromBlocks 1 (-Q) (-R) 1 * CmI n * (Cm n * Matrix.fromBlocks 1 Q R 1 * CmI n)
              = Cm n * (Matrix.fromBlocks 1 (-Q) (-R) 1 * (CmI n * Cm n) * Matrix.fromBlocks 1 Q R 1) * CmI n := by
                simp only [Matrix.mul_assoc]
            _ = 1 := by rw [CmI_mul_Cm, Matrix.mul_one, hfb, Matrix.mul_one, Cm_mul_CmI]
  rw [ub1, hinv, ub_eq, ← Matrix.mul_assoc (Lr n), Lr_mX, Matrix.mul_assoc, inv_blocks_of_InG hx, Rc,
    Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows]
  simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_I, Matrix.mul_one, Matrix.mul_zero, add_zero, sub_neg_eq_add, neg_neg,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, neg_smul, smul_neg]
  module
end PositivityTheory.Rg.Sw.LVs
