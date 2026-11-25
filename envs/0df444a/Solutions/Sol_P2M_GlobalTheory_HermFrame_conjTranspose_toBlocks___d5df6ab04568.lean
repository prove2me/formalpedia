-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_conjTranspose_toBlocks___d5df6ab04568
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:07.451006+00:00
-- url     : https://prove2.me/submissions/a6685d4b-416b-4f1b-86b8-65b0e54282a6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
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
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : H.IsHermitian) : H.toBlocks₁₂ᴴ = H.toBlocks₂₁ := by
  ext i j; exact h.apply _ _
end GlobalTheory.HermFrame
