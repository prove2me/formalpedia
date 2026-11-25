-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.sumA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:05.350315+00:00
-- url     : https://prove2.me/submissions/aa019508-6c54-4727-8631-7ca34b72cded

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_eA_mul_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_mul_eA_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (M : M2 n) : ∑ a, ∑ b, ((eA a b * M - M * eA a b : M2 n) (Sum.inr a) (Sum.inr b)) = 0 := by
  simp only [Matrix.sub_apply, eA_mul_apply, mul_eA_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => M (Sum.inr b) (Sum.inr b))]
  simp
end PositivityTheory.Rg.Sw.LVs.II
