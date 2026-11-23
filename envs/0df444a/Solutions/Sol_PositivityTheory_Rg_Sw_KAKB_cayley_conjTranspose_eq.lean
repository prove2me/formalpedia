-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.KAKB.cayley_conjTranspose_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:04.553038+00:00
-- url     : https://prove2.me/submissions/f2e152ae-3787-4db8-a6b4-a1caca25df66

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
theorem _root_.solution : (C0 n)ᴴ = fromBlocks 1 (-(Complex.I • 1)) 1 (Complex.I • 1) := by
  simp [C0, fromBlocks_conjTranspose, conjTranspose_smul]
end PositivityTheory.Rg.Sw.KAKB
