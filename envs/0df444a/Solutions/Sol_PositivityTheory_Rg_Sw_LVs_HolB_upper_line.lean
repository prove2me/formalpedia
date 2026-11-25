-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolB.upper_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:27.334939+00:00
-- url     : https://prove2.me/submissions/4da44817-2682-4693-907f-4c2dd45dd655

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
theorem _root_.solution (y : M2 n) (b : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 b 0 0) = y * fromBlocks 1 (t • b) 0 1 := by
  have e : (fromBlocks 1 (t • b) 0 1 : M2 n) = 1 + t • fromBlocks 0 b 0 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]
end PositivityTheory.Rg.Sw.LVs.HolB
