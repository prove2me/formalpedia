-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.det_par
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:03.734869+00:00
-- url     : https://prove2.me/submissions/eab75795-8316-4a50-9094-f723cb4341ec

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
theorem _root_.solution {P : M2 n} (hP : P.toBlocks₂₁ = 0) : P.det = P.toBlocks₁₁.det * P.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks P, hP]
  exact det_fromBlocks_zero₂₁ _ _ _
end PositivityTheory.Rg.Sw.LVs
