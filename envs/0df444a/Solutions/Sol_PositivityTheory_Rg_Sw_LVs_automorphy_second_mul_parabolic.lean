-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.automorphy_second_mul_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:08.087143+00:00
-- url     : https://prove2.me/submissions/a8e7939c-bce8-4c3e-a991-0605b362e0ce

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u2 (P * x) = P.toBlocks₂₂ * u2 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u2, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]
end PositivityTheory.Rg.Sw.LVs
