-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_isUnit_det_blockDiagonal__96e6d9fa8b0a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:56.630013+00:00
-- url     : https://prove2.me/submissions/c1d475f4-03c1-4f09-a586-a96ab4af9df0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {o : Type*} [DecidableEq o] {m m' : o → Type*}
variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]
variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, IsUnit (A i).det) :
    IsUnit (blockDiagonal' A).det := by
  refine isUnit_det_of_right_inverse (B := blockDiagonal' fun i => (A i)⁻¹) ?_
  rw [← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext i
  exact mul_nonsing_inv _ (h i)
end GlobalTheory.HermFrame
