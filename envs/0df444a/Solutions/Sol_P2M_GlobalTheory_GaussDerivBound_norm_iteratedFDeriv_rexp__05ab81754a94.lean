-- Prove2me | solution 1 for P2M_GlobalTheory_GaussDerivBound_norm_iteratedFDeriv_rexp__05ab81754a94
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:45.886389+00:00
-- url     : https://prove2.me/submissions/cb508802-c998-4e02-a94e-91b44db70682

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianIteratedFDerivWeightedExpBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussDerivBound
open scoped Nat
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.GaussDerivBound
theorem _root_.solution (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
end GlobalTheory.GaussDerivBound
