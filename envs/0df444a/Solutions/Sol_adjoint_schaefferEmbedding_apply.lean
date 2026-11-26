-- Prove2me | solution 1 for adjoint_schaefferEmbedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:15.718958+00:00
-- url     : https://prove2.me/submissions/bc1b9a64-4f5f-4c94-819b-2d926e934437

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
theorem _root_.solution (f : SchaefferSpace E) :
    ContinuousLinearMap.adjoint (schaefferEmbedding : E →L[ℂ] SchaefferSpace E) f = f 0 := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [schaefferEmbedding_apply, lp.inner_single_right]
