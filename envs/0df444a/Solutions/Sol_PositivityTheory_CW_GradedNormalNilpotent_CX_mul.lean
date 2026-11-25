-- Prove2me | solution 1 for PositivityTheory.CW.GradedNormalNilpotent.CX_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:22:32.519156+00:00
-- url     : https://prove2.me/submissions/1c0b5b64-b8cb-4947-8bd2-9a2d842d06b9

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_coe_L
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.CW.GradedNormalNilpotent.coe_L

set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.GradedNormalNilpotent
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
variable {ε E}
variable (h : Hyp ε E)
namespace PositivityTheory.CW.GradedNormalNilpotent
theorem _root_.solution (x y : Module.End ℂ V) (i j : ℕ) :
    (C x * X ^ i) * (C y * X ^ j) = C (x * y) * X ^ (i + j) := by
  calc (C x * X ^ i) * (C y * X ^ j) = C x * (X ^ i * C y) * X ^ j := by simp only [mul_assoc]
    _ = C x * (C y * X ^ i) * X ^ j := by rw [(Polynomial.commute_X_pow (C y) i).eq]
    _ = C (x * y) * X ^ (i + j) := by simp only [mul_assoc, C_mul, pow_add]
end PositivityTheory.CW.GradedNormalNilpotent
