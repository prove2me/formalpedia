-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.cmH_JJ_cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:34.807491+00:00
-- url     : https://prove2.me/submissions/45c27464-3cc5-4d1b-b6e5-de72971c44b5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-(2 * Complex.I)) • 1) 0 0 ((2 * Complex.I) • 1) := by
  rw [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp [smul_smul]
  refine ⟨?_, ?_⟩
  · rw [← neg_add, ← add_smul, two_mul]
  · rw [← add_smul, two_mul]
end PositivityTheory.Rg.Sw.LVs.TC
