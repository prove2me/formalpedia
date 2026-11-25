-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_mContDiffAt_blockDiagonal__bc50d51f27b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:13.498564+00:00
-- url     : https://prove2.me/submissions/a66eff8a-148a-4365-b7f5-e24d33387994

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
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
namespace GlobalTheory.HermFrame
theorem _root_.solution {k : WithTop ℕ∞} {A : ∀ i, E → Matrix (m i) (m' i) ℂ} {z : E}
    (hA : ∀ i, MContDiffAt k (A i) z) :
    MContDiffAt k (fun x => blockDiagonal' fun i => A i x) z := by
  rintro ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simpa using hA i a b
  · simpa [blockDiagonal'_apply_ne _ _ _ h] using contDiffAt_const
end GlobalTheory.HermFrame
