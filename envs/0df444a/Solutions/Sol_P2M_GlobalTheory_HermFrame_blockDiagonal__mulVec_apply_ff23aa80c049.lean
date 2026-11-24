-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_blockDiagonal__mulVec_apply_ff23aa80c049
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:13.260176+00:00
-- url     : https://prove2.me/submissions/99ce867f-24d1-4f79-821b-bc8a143863b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
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
omit [∀ i, Fintype (m' i)]
namespace GlobalTheory.HermFrame
theorem _root_.solution (T : ∀ i, Matrix (m' i) (m i) ℂ) (v : (Σ i, m i) → ℂ) (i : o)
    (a : m' i) : (blockDiagonal' T *ᵥ v) ⟨i, a⟩ = (T i *ᵥ fun b => v ⟨i, b⟩) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [blockDiagonal'_apply_ne _ _ _ hj.symm]
  · simp
end GlobalTheory.HermFrame
