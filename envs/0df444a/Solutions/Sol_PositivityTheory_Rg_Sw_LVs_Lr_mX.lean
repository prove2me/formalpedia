-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.Lr_mX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:48:06.0223+00:00
-- url     : https://prove2.me/submissions/b4d3bb05-db69-41fd-a9b6-e46f06d3b08b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_Cm_inv

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
theorem _root_.solution (Q R : Matrix (Fin n) (Fin n) ℂ) :
    (Lr n * mX 1 Q R 1 : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = Matrix.fromCols (1 - Q) (Complex.I • (1 + Q)) := by
  have hI : (-(Complex.I / 2)) * (2 * Complex.I) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_mul_I
  have hI2 : (-(Complex.I / 2)) * (2 * Complex.I * Complex.I) = Complex.I := by
    linear_combination (-Complex.I) * Complex.I_mul_I
  have e1 : (Lr n * Cm n : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) =
      (Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) (0 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [Lr, Cm, Matrix.fromCols_mul_fromBlocks]
    congr 1
    · simp only [Matrix.one_mul, Matrix.mul_one]; module
    · simp only [Matrix.one_mul, Matrix.mul_one]; module
  have e2 : ((Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) (0 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) Q R 1 :
        Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) =
      (Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ((2 * Complex.I) • Q) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [Matrix.fromCols_mul_fromBlocks]
    simp
  have e3 : ((Matrix.fromCols ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ((2 * Complex.I) • Q) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * CmI n :
        Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) = Matrix.fromCols (1 - Q) (Complex.I • (1 + Q)) := by
    rw [CmI, Matrix.mul_smul, Matrix.fromCols_mul_fromBlocks]
    ext a b
    rcases b with b | b
    · simp only [Matrix.smul_apply, Matrix.fromCols_apply_inl, Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_apply, Matrix.sub_apply, smul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq]
        linear_combination (1 - Q a a) * hI
      · simp only [Matrix.one_apply_ne hab]
        linear_combination (- Q a b) * hI
    · simp only [Matrix.smul_apply, Matrix.fromCols_apply_inr, Matrix.add_apply, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq]
        linear_combination (1 + Q a a) * hI2
      · simp only [Matrix.one_apply_ne hab]
        linear_combination (Q a b) * hI2
  rw [mX, dp_Cm_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, e2, e3]
end PositivityTheory.Rg.Sw.LVs
