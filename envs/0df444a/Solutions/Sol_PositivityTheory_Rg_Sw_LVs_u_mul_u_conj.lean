-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.u_mul_u_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:25.635091+00:00
-- url     : https://prove2.me/submissions/b0545c6c-374c-423f-ad1a-587379464c9b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_blocks_of_InG

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {x : M2 n} (hx : InG x) : u1 x * (u1 x)ᴴ = u2 x * (u2 x)ᴴ := by
  have h := (blocks_of_InG hx).1
  simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
    Complex.star_def, Complex.conj_I]
  rw [h]
  module
end PositivityTheory.Rg.Sw.LVs
