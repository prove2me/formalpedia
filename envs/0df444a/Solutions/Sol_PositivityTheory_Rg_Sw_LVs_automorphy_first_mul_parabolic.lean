-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.automorphy_first_mul_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:34.481805+00:00
-- url     : https://prove2.me/submissions/479493a6-5cf7-41e0-9eb3-2d697a8c4f00

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
theorem _root_.solution {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u1 (P * x) = P.toBlocks₂₂ * u1 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul]
end PositivityTheory.Rg.Sw.LVs
