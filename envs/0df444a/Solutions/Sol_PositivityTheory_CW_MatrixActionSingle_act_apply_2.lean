-- Prove2me | solution 2 for PositivityTheory.CW.MatrixActionSingle.act_apply
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T22:51:14.434156+00:00
-- url     : https://prove2.me/submissions/45ba2621-b989-46d0-b688-b0a72a8c2b7e

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.MatrixActionSingle
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem solution (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (u : PiLp 2 fun _ : Fin n => V) (a : Fin n) :
    act A u a = ∑ b, A a b (u b) := by
  rfl
