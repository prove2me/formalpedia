-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.par_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:54.276984+00:00
-- url     : https://prove2.me/submissions/24f7932f-c969-4da3-9ea5-6f2fc92b2bca

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
theorem _root_.solution {P : M2 n} (hG : InG P) (hP : P.toBlocks₂₁ = 0) : P.toBlocks₁₁ᴴ * P.toBlocks₂₂ = 1 := by
  have h := congrArg Matrix.toBlocks₁₂ hG
  rw [← fromBlocks_toBlocks P, hP] at h
  simpa [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] using h
end PositivityTheory.Rg.Sw.LVs
