-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cm_mul_cmi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:29.358854+00:00
-- url     : https://prove2.me/submissions/054ca2d5-96fe-4632-8416-7a61f3a9ec2d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : Cm n * Cmi n = 1 := by
  rw [Cm, Cmi, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases h : i = j <;>
    simp [Matrix.one_apply, h, Matrix.add_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf
end PositivityTheory.Rg.Sw.LVs
