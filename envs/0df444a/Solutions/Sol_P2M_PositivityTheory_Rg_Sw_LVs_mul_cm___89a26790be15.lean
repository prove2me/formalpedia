-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___89a26790be15
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:59.285158+00:00
-- url     : https://prove2.me/submissions/eaed541e-d52c-4352-80cb-e04ff2b93a7c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_03bb7bc462ab

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
theorem _root_.solution (x : M2 n) : (x * Cm n).toBlocks₂₁ = u1 x := by
  rw [toBlocks₂₁_mul, u1, Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one]
end PositivityTheory.Rg.Sw.LVs
