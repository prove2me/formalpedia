-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_form_blockDiagonal__1704ae5cb2fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:09.971874+00:00
-- url     : https://prove2.me/submissions/dfb7d7ca-acbc-41e9-bf83-ef6e669484ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
import Theorems.Thm_P2M_GlobalTheory_HermFrame_blockDiagonal__mulVec_apply_ff23aa80c049
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {o : Type*} [DecidableEq o] {m m' : o → Type*}
variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]
namespace GlobalTheory.HermFrame
theorem _root_.solution (A : ∀ i, Matrix (m i) (m i) ℂ) (v w : (Σ i, m i) → ℂ) :
    form (blockDiagonal' A) v w = ∑ i, form (A i) (fun a => v ⟨i, a⟩) fun a => w ⟨i, a⟩ := by
  simp only [form, dotProduct, Fintype.sum_sigma, blockDiagonal'_mulVec_apply]
  rfl
end GlobalTheory.HermFrame
