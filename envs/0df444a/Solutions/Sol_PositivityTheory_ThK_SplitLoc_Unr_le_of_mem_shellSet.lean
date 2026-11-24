-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.le_of_mem_shellSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:37.931466+00:00
-- url     : https://prove2.me/submissions/5fc4bdf5-352b-462b-a234-2606a378ff09

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_WeightedSummable_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitFlip_mem_shellSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open GlobalTheory.IwahoriInj
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {e : Fin n → ℤ} {g : GL (Fin n) k}
    (hg : g ∈ shellSet ϖ e) {a : ℤ} (ha : ∀ i j, Deep a (g.val i j)) (i : Fin n) : a ≤ e i := by
  obtain ⟨x, hx, y, hy, h⟩ := mem_shellSet.1 hg
  have h1 : (diagGL fun i => ϖ ^ e i) = x⁻¹ * g * y⁻¹ := by rw [h]; group
  have hx' : ∀ i j, Deep 0 ((x⁻¹).val i j) := fun i j => deep_zero_iff.2 (((mem_KO_iff x).1 hx).2 i j)
  have hy' : ∀ i j, Deep 0 ((y⁻¹).val i j) := fun i j => deep_zero_iff.2 (((mem_KO_iff y).1 hy).2 i j)
  have h2 : Deep a ((x⁻¹ * g * y⁻¹).val i i) := by
    rw [Units.val_mul, Units.val_mul, mul_apply]
    refine Deep.sum fun l _ => ?_
    have h3 : Deep a (((x⁻¹).val * g.val) i l) := by
      rw [mul_apply]
      exact Deep.sum fun r _ => ((hx' i r).mul (ha r l)).mono (by omega)
    exact (h3.mul (hy' l i)).mono (by omega)
  rw [← h1, diagGL_val, diagonal_apply_eq, Deep, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ] at h2
  exact (zpow_le_zpow_iff_right_of_lt_one₀ unif_pos uniformizer_lt_one).1 h2
end PositivityTheory.ThK.SplitLoc.Unr
