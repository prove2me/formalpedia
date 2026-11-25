-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.smul_conjCm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:19.53311+00:00
-- url     : https://prove2.me/submissions/e83f792b-45be-40bb-a28d-70a00c0abe07

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
theorem _root_.solution (c : ℂ) (X : M2 n) : c • (Cm n * X * CmI n) = Cm n * (c • X) * CmI n := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
end PositivityTheory.Rg.Sw.LVs.TC
