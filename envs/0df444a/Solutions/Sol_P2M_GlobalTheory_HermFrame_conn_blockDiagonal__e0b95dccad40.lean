-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_conn_blockDiagonal__e0b95dccad40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:29.30173+00:00
-- url     : https://prove2.me/submissions/d6746480-721c-4f41-906b-9dcf55bb5a25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
import Theorems.Thm_P2M_GlobalTheory_HermFrame_mdel_blockDiagonal__bdefd5e2542e
import Theorems.Thm_P2M_GlobalTheory_HermFrame_isUnit_det_blockDiagonal__96e6d9fa8b0a

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
theorem _root_.solution (h : ∀ i, IsUnit (H i z).det) (ξ : E) :
    conn (fun x => blockDiagonal' fun i => H i x) z ξ = blockDiagonal' fun i => conn (H i) z ξ := by
  refine (eq_conn_of_compatible (H := fun x => blockDiagonal' fun i => H i x)
    (isUnit_det_blockDiagonal' h) ?_).symm
  rw [mdel_blockDiagonal', blockDiagonal'_transpose, ← blockDiagonal'_mul]
  congr 1
  funext i
  exact conn_transpose_mul (h i) ξ
end GlobalTheory.HermFrame
