-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:35:37.991546+00:00
-- url     : https://prove2.me/submissions/69c9fbd3-a693-4a02-9520-a427e9583dd8

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
theorem _root_.solution {F L : Type*} [Field F] [Field L] [Algebra F L] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (a : Basis κ F L) (h : L) :
    (Matrix.of fun p q => Algebra.trace F L (h * a p * a q)).det =
      Algebra.norm F h * Algebra.discr F a := by

  rw [Algebra.discr_def, Algebra.norm_eq_matrix_det a h,
    ← Matrix.det_transpose (Algebra.leftMulMatrix a h), ← Matrix.det_mul]
  congr 1
  ext p q
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [← a.sum_repr (h * a p)]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
