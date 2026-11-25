-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_gnorm_blockDiagonal__sq_8b738351c48d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:24.327279+00:00
-- url     : https://prove2.me/submissions/3aabfb93-21ac-42cb-b49a-90959b945a40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
import Theorems.Thm_P2M_GlobalTheory_HermFrame_form_blockDiagonal__1704ae5cb2fa
import Theorems.Thm_P2M_GlobalTheory_HermFrame_posSemidef_blockDiagonal__a5251a6bbb88
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_sq
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
theorem _root_.solution {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef)
    (v : (Σ i, m i) → ℂ) :
    gnorm (blockDiagonal' A) v ^ 2 = ∑ i, gnorm (A i) (fun a => v ⟨i, a⟩) ^ 2 := by
  simp only [gnorm_sq (posSemidef_blockDiagonal' h), gnorm_sq (h _), form_blockDiagonal', re_sum]
end GlobalTheory.HermFrame
