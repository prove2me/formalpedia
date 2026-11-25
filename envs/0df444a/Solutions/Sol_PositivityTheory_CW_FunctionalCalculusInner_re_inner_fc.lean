-- Prove2me | solution 1 for PositivityTheory.CW.FunctionalCalculusInner.re_inner_fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:49.032096+00:00
-- url     : https://prove2.me/submissions/5851e596-4c89-4f71-b0aa-99dfcf5a000a

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_repr_fc
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_inner_eq_sum
import Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_re_conj_mul

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
theorem _root_.solution (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (w : V) :
    (inner ℂ w (fc b μ φ w)).re = ∑ i ∈ (b.repr w).support, φ (μ i) * ‖b.repr w i‖ ^ 2 := by
  rw [inner_eq_sum b hb w _ _ subset_rfl, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_fc, re_conj_mul]
end PositivityTheory.CW.FunctionalCalculusInner
