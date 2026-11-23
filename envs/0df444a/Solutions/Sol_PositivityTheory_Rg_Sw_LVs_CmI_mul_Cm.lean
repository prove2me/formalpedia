-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CmI_mul_Cm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:22.765576+00:00
-- url     : https://prove2.me/submissions/3b699afb-cfc7-4b85-a1b0-35da6fb0568e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

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
theorem _root_.solution : CmI n * Cm n = 1 := by
  have hI : (-(Complex.I / 2)) * (2 * Complex.I) = 1 := by
    linear_combination (-1 : ℂ) * Complex.I_mul_I
  rw [CmI, Cm, Matrix.smul_mul, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  congr 1
  · rw [show (1 : Matrix (Fin n) (Fin n) ℂ) * (Complex.I • 1) + (Complex.I • 1) * 1 = (2 * Complex.I) • 1 by
      simp only [Matrix.one_mul, Matrix.mul_one]; module, smul_smul, hI, one_smul]
  · rw [show (1 : Matrix (Fin n) (Fin n) ℂ) * -(Complex.I • 1) + (Complex.I • 1) * 1 = 0 by
      simp only [Matrix.one_mul, Matrix.mul_one]; module, smul_zero]
  · rw [show (-1 : Matrix (Fin n) (Fin n) ℂ) * (Complex.I • 1) + (Complex.I • 1) * 1 = 0 by
      simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_one]; module, smul_zero]
  · rw [show (-1 : Matrix (Fin n) (Fin n) ℂ) * -(Complex.I • 1) + (Complex.I • 1) * 1 = (2 * Complex.I) • 1 by
      simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul, Matrix.mul_one]; module, smul_smul, hI,
      one_smul]
end PositivityTheory.Rg.Sw.LVs
