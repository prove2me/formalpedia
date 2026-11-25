-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.rot_nU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:55.87794+00:00
-- url     : https://prove2.me/submissions/4eab70ce-4110-45c3-ab8a-9b236e8e6e6c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompC
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rotL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_nU_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rot_mul_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.TC.rotL_apply

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    g * rot j θ * nU H * (rot j θ)⁻¹ = g + rotL g j θ H := by
  simp only [nU_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, rot_mul_inv, rotL_apply]
end PositivityTheory.Rg.Sw.LVs.TC
