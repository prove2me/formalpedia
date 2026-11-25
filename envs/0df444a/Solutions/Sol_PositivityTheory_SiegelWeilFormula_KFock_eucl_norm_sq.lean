-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFock.eucl_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:27.190222+00:00
-- url     : https://prove2.me/submissions/05bbddf2-07ec-46b5-a87a-1b00c4f234fc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_EvXTemperate
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory.Rg.Sw
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock
namespace PositivityTheory.SiegelWeilFormula.KFock
theorem _root_.solution (m n : ℕ) (s : ℝ) (hs : s ≠ 0) (x : Fin m → Fin n → ℂ) :
    ‖eucl m n s hs x‖ ^ 2 = s ^ 2 * ∑ a, ∑ i, ‖x a i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eucl, norm_smul, mul_pow]
end PositivityTheory.SiegelWeilFormula.KFock
