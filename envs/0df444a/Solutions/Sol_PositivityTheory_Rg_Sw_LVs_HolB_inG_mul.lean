-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolB.inG_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.962415+00:00
-- url     : https://prove2.me/submissions/45645600-4914-4ea3-bbe3-fec1e086cbda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HermRealSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.HolB
theorem _root_.solution {a b : M2 n} (ha : InG a) (hb : InG b) : InG (a * b) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [ha, hb]
end PositivityTheory.Rg.Sw.LVs.HolB
