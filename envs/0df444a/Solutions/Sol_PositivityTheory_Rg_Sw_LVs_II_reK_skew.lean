-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.reK_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:24.383387+00:00
-- url     : https://prove2.me/submissions/d88b92fc-0b3f-40ba-b541-ad268286f6ef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (e : M2 n) : (reK e)ᴴ = -reK e := by
  ext i j
  simp only [reK, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
end PositivityTheory.Rg.Sw.LVs.II
