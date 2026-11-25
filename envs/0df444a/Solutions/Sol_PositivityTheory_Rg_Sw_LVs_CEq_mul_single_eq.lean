-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.mul_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:37.559488+00:00
-- url     : https://prove2.me/submissions/2fb00fca-621e-4979-889b-f80c3b2f10dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq

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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [Fintype ι]
namespace PositivityTheory.Rg.Sw.LVs.CEq
theorem _root_.solution [Fintype ι] (A : Matrix ι ι ℂ) (a b : ι) :
    A * Matrix.single a b (1 : ℂ) = ∑ c, A c a • Matrix.single c b (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]
end PositivityTheory.Rg.Sw.LVs.CEq
