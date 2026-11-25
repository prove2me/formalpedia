-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolB.inG_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:42.938699+00:00
-- url     : https://prove2.me/submissions/6a8359fb-11fc-4edb-963b-be37d8e47f80

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
theorem _root_.solution {c : ℂ} (hc : star c * c = 1) : InG (c • (1 : M2 n)) := by
  show (c • (1 : M2 n))ᴴ * JJ n * (c • (1 : M2 n)) = JJ n
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, hc, one_smul]
end PositivityTheory.Rg.Sw.LVs.HolB
