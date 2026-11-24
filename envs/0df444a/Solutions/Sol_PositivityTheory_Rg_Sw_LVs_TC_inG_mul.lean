-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.inG_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.768372+00:00
-- url     : https://prove2.me/submissions/bfb162f7-28c3-4def-8a46-6507b7e60711

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
theorem _root_.solution {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul, show hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h by simp only [Matrix.mul_assoc], hg, hh]
end PositivityTheory.Rg.Sw.LVs.TC
