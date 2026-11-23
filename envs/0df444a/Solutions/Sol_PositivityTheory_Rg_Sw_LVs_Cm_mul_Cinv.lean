-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.Cm_mul_Cinv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:23.492708+00:00
-- url     : https://prove2.me/submissions/a37170c5-2d83-4531-a4be-0461f4ef4cd6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : Cm n * Cinv n = 1 := by
  have hI : (2 * Complex.I) ≠ 0 := by simp
  rw [Cm, Cinv, Matrix.mul_smul, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;>
    simp only [Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.neg_apply,
      smul_eq_mul, Matrix.smul_apply] <;>
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, one_mul, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    split_ifs <;> (try simp_all) <;> (try split_ifs) <;> (try simp_all) <;> (try field_simp) <;> (try ring_nf) <;> (try simp [Complex.I_sq]) <;> (try ring_nf)
end PositivityTheory.Rg.Sw.LVs
