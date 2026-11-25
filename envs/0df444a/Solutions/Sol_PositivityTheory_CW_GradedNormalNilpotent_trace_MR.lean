-- Prove2me | solution 1 for PositivityTheory.CW.GradedNormalNilpotent.trace_MR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:24:54.637209+00:00
-- url     : https://prove2.me/submissions/b00316a7-8adf-4c72-936d-1654a753c7b8

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (j : ℕ) (hM : ∀ a b, M a b ∈ U E j)
    (hT : M.trace ∈ U E j) : ((psi h).mapMatrix (MR h M j hM)).trace = psi h (L h j M.trace hT) := by
  have : L h j M.trace hT = ∑ i, MR h M j hM i i := by
    apply Subtype.ext
    simp [MR, Matrix.trace, Finset.sum_mul]
  rw [this, map_sum]
  rfl
end PositivityTheory.CW.GradedNormalNilpotent
