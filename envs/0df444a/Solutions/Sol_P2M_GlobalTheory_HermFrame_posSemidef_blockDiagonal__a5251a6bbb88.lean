-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_posSemidef_blockDiagonal__a5251a6bbb88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:37.922146+00:00
-- url     : https://prove2.me/submissions/33e04923-aa0b-43e1-8f64-bb5d45f1631f

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
theorem _root_.solution {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef) :
    (blockDiagonal' A).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_blockDiagonal'_iff.2 fun i => (h i).isHermitian) fun x => ?_
  simp only [dotProduct, Fintype.sum_sigma, blockDiagonal'_mulVec_apply]
  exact Finset.sum_nonneg fun i _ => (h i).dotProduct_mulVec_nonneg fun a => x ⟨i, a⟩
end GlobalTheory.HermFrame
