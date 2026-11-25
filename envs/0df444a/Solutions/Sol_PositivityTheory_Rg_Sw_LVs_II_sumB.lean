-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.sumB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:38.380796+00:00
-- url     : https://prove2.me/submissions/8ad8d0b8-679f-4e19-8d73-3ab0b54c0329

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__bfe685cdc5a1
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__f3b15b56784f
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_eB_mul_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_mul_eB_apply

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
theorem _root_.solution (M : M2 n) : ∑ a, ∑ b, -((eB a b * M - M * eB a b : M2 n) (Sum.inr a) (Sum.inl b)) =
    (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) := by
  simp only [Matrix.sub_apply, eB_mul_apply, mul_eB_apply, neg_sub, neg_neg, sub_neg_eq_add, Finset.sum_sub_distrib]
  simp only [Matrix.trace, Matrix.diag, toBlocks₁₁_apply', toBlocks₂₂_apply', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub]
  have h : ∀ a b : Fin n, -(-M (Sum.inl b) (Sum.inl b) + M (Sum.inr a) (Sum.inr a)) =
      M (Sum.inl b) (Sum.inl b) - M (Sum.inr a) (Sum.inr a) := fun _ _ => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum]
end PositivityTheory.Rg.Sw.LVs.II
