-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.reindex_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:39.814806+00:00
-- url     : https://prove2.me/submissions/6f4233c5-362b-45b7-b49c-7d1dca48b87e

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
omit [DecidableEq ι] [DecidableEq κ]
namespace PositivityTheory.Rg.Sw.LVs.CEq
theorem _root_.solution [DecidableEq ι] [DecidableEq κ] (e' : ι ≃ κ) (a b : ι) :
    (Matrix.single a b (1 : ℂ)).reindex e' e' = Matrix.single (e' a) (e' b) 1 := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply, Equiv.eq_symm_apply]
end PositivityTheory.Rg.Sw.LVs.CEq
