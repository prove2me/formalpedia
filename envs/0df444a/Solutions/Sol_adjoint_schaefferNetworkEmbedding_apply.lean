-- Prove2me | solution 1 for adjoint_schaefferNetworkEmbedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:54.692515+00:00
-- url     : https://prove2.me/submissions/64e59031-d9c7-433b-9a6c-9c710ce49f4c

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Operator_Dilation_Halmos
import Definitions.Def_Operator_Dilation_Schaeffer

set_option autoImplicit false
open scoped ENNReal InnerProductSpace
universe u
noncomputable section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (f : SchaefferNetworkSpace E) :
    ContinuousLinearMap.adjoint
      (schaefferNetworkEmbedding : E →L[ℂ] SchaefferNetworkSpace E) f = (f 0).fst := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [schaefferNetworkEmbedding_apply, lp.inner_single_right,
    WithLp.prod_inner_apply, inner_zero_right, add_zero]
  rfl
