-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.star_exp_negI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:16.692778+00:00
-- url     : https://prove2.me/submissions/dbbfe81a-2bf9-4b1a-b80b-413c44a04480

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI

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
theorem _root_.solution (θ : ℝ) : star (Complex.exp (-θ * Complex.I)) * Complex.exp (-θ * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp
end PositivityTheory.Rg.Sw.LVs.TC
