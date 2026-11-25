-- Prove2me | solution 1 for PositivityTheory.CW.GradedNormalNilpotent.psiL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:24:50.548156+00:00
-- url     : https://prove2.me/submissions/2ede45d7-603b-4ca9-af7a-6fdaaceb75d1

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
theorem _root_.solution (j : ℕ) (x : Module.End ℂ V) (hx : x ∈ U E j) : psi h (L h j x hx) = 0 ↔ x ∈ Jk ε E j := by
  rw [← map_zero (psi h)]
  change ((L h j x hx : Rr ε E h) : Q ε E h) = ((0 : Rr ε E h) : Q ε E h) ↔ _
  rw [RingCon.eq]
  change inJ ε E (C x * X ^ j - 0) ↔ _
  simp only [sub_zero, inJ, coeff_C_mul_X_pow]
  constructor
  · intro H; simpa using H j
  · intro H k; split_ifs with hk
    · subst hk; exact H
    · exact zero_mem _
end PositivityTheory.CW.GradedNormalNilpotent
