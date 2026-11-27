-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_posDef_blockDiagonal__3fab605ad041
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:09.152619+00:00
-- url     : https://prove2.me/submissions/e870e5aa-ae99-40f1-b57c-9d268340106f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
import Theorems.Thm_P2M_GlobalTheory_HermFrame_posSemidef_blockDiagonal__a5251a6bbb88
import Theorems.Thm_P2M_GlobalTheory_HermFrame_gnorm_blockDiagonal__sq_8b738351c48d
import Theorems.Thm_GlobalTheory_HermFrame_form_self


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
namespace GlobalTheory.HermFrame
theorem _root_.solution {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosDef) :
    (blockDiagonal' A).PosDef := by
  refine posDef_iff.2 ⟨isHermitian_blockDiagonal'_iff.2 fun i => (h i).isHermitian,
    fun v hv => ?_⟩
  rw [form_self (posSemidef_blockDiagonal' fun i => (h i).posSemidef),
    gnorm_blockDiagonal'_sq fun i => (h i).posSemidef, zero_lt_real]
  obtain ⟨⟨i, a⟩, ha⟩ := Function.ne_iff.1 hv
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _,
    pow_pos (gnorm_pos (h i) (Function.ne_iff.2 ⟨a, ha⟩)) 2⟩
end GlobalTheory.HermFrame
