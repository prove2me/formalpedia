-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_isHermFrame_blockDiagonal__b858d1ae694e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:51:02.694007+00:00
-- url     : https://prove2.me/submissions/72f57f77-8939-4137-a0c8-f3e80b47f077

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
import Theorems.Thm_P2M_GlobalTheory_HermFrame_mContDiffAt_blockDiagonal__bc50d51f27b0
import Theorems.Thm_P2M_GlobalTheory_HermFrame_isUnit_det_blockDiagonal__96e6d9fa8b0a
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_mContDiffAt
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_of_mContDiffAt


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
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
namespace GlobalTheory.HermFrame
theorem _root_.solution {U : Set E} (hU : IsOpen U) (h : ∀ i, IsHermFrame U (H i)) :
    IsHermFrame U fun x => blockDiagonal' fun i => H i x :=
  .of_mContDiffAt hU (fun _ hz => mContDiffAt_blockDiagonal' fun i => (h i).mContDiffAt hz)
    (fun z hz => isHermitian_blockDiagonal'_iff.2 fun i => (h i).herm z hz)
    fun z hz => isUnit_det_blockDiagonal' fun i => (h i).isUnit z hz
end GlobalTheory.HermFrame
