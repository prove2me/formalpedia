-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.imK_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:47.77138+00:00
-- url     : https://prove2.me/submissions/838f71d1-8040-4330-9c2f-9792bc422d41

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_comm_conjT

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
theorem _root_.solution {e : M2 n} (he : e * JJ n = JJ n * e) : imK e * JJ n = JJ n * imK e := by
  unfold imK
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, he, comm_conjT he]
end PositivityTheory.Rg.Sw.LVs.II
