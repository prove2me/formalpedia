-- Prove2me | solution 1 for PositivityTheory.CW.GradedNormalNilpotent.MR_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:27.313356+00:00
-- url     : https://prove2.me/submissions/85011646-a79a-4710-b2ef-319eb9752ec3

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_coe_L
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_CX_mul
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
theorem _root_.solution (M M' : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (i j : ℕ) (hM : ∀ a b, M a b ∈ U E i)
    (hM' : ∀ a b, M' a b ∈ U E j) :
    ∃ h'' : ∀ a b, (M * M') a b ∈ U E (i + j), MR h M i hM * MR h M' j hM' = MR h (M * M') (i + j) h'' := by
  refine ⟨fun a b => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun c _ => h.mul _ _ _ (hM a c) _ (hM' c b)
  · refine Matrix.ext fun a b => Subtype.ext ?_
    simp only [Matrix.mul_apply, MR, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, coe_L, CX_mul, map_sum,
      Finset.sum_mul]
end PositivityTheory.CW.GradedNormalNilpotent
