-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.KAKB.complex_structure_cayley
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:48.461034+00:00
-- url     : https://prove2.me/submissions/74f6d67f-a9e2-40ce-b4ae-8c50b644d6c1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_CayleyMulConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Matrix
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.KAKB
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.KAKB
theorem _root_.solution : JJ n * C0 n = C0 n * (Complex.I • S0 n) := by
  simp only [JJ, C0, S0, fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul] <;> module
end PositivityTheory.Rg.Sw.KAKB
