-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.jj_mul_jj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:40.646256+00:00
-- url     : https://prove2.me/submissions/d3aca3e5-6a02-4d7b-a6f4-ba69afb0cf05

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatA
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp
end PositivityTheory.Rg.Sw.LVs.TC
