-- Prove2me | solution 1 for PositivityTheory.CW.FunctionalCalculusInner.inner_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:25.520887+00:00
-- url     : https://prove2.me/submissions/92c3830c-95dc-4794-85da-76b863267333

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_inner_basis_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FunctionalCalculusInner
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
namespace PositivityTheory.CW.FunctionalCalculusInner
theorem _root_.solution (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (x y : V) (s : Finset ι)
    (hs : (b.repr x).support ⊆ s) :
    inner ℂ x y = ∑ i ∈ s, starRingEnd ℂ (b.repr x i) * b.repr y i := by
  have hx : x = ∑ i ∈ s, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs]
    intro i _
    simp
  conv_lhs => rw [hx]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_basis_left b hb]
end PositivityTheory.CW.FunctionalCalculusInner
