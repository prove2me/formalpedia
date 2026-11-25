-- Prove2me | solution 1 for PositivityTheory.CW.GradedNormalNilpotent.MR_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:25.060467+00:00
-- url     : https://prove2.me/submissions/f8bde6a2-c74f-4282-81f6-01920da96fc3

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_coe_L
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_MR_mul
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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j) (k : ℕ) :
    ∃ hk : ∀ a b, (M ^ (k + 1)) a b ∈ U E (j * (k + 1)), MR h M j hM ^ (k + 1) = MR h (M ^ (k + 1)) (j * (k + 1)) hk := by
  induction k with
  | zero =>
    refine ⟨fun a b => by simpa using hM a b, ?_⟩
    refine Matrix.ext fun a b => Subtype.ext ?_; simp [MR]
  | succ k ih =>
    obtain ⟨hk, e⟩ := ih
    obtain ⟨h'', e'⟩ := MR_mul h _ M _ j hk hM
    refine ⟨fun a b => ?_, ?_⟩
    · have := h'' a b; rwa [← pow_succ, show j * (k + 1) + j = j * (k + 1 + 1) by ring] at this
    · rw [pow_succ, e, e']
      refine Matrix.ext fun a b => Subtype.ext ?_
      simp only [MR, coe_L, ← pow_succ, show j * (k + 1) + j = j * (k + 1 + 1) by ring]
end PositivityTheory.CW.GradedNormalNilpotent
