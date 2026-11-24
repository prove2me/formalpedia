-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.exists_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:36:50.822256+00:00
-- url     : https://prove2.me/submissions/3de531af-07c1-4211-bd18-d7bf45bda2a0

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_SBUniform_exists_bound_period


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
variable [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) :
    ∃ N M : ℕ, (∀ x, φ ((scal n (ϖ ^ N)⁻¹).val * x) ≠ 0 → ∀ i j, x i j ∈ 𝒪[k]) ∧
      ∀ x y : Matrix (Fin n) (Fin n) k, (∀ i j, valuation k (y i j) ≤ valuation k (ϖ : k) ^ M) →
        φ ((scal n (ϖ ^ N)⁻¹).val * (x + y)) = φ ((scal n (ϖ ^ N)⁻¹).val * x) := by
  obtain ⟨N, M, hN, hM⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin n) φ hφ
  have hval : ∀ (x : Matrix (Fin n) (Fin n) k) i j,
      valuation k (((scal n (ϖ ^ N)⁻¹).val * x) i j) = uniformizer k ^ (-(N : ℤ)) * valuation k (x i j) := by
    intro x i j
    rw [scal, diagGL_val, diagonal_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow,
      hϖ, _root_.zpow_neg, zpow_natCast]
  have hpos : 0 < uniformizer k := GlobalTheory.IwahoriInj.unif_pos
  refine ⟨N, M + N, fun x hx i j => ?_, fun x y hy => ?_⟩
  · have h : valuation k _ ≤ _ := hN _ hx i j
    rw [hval] at h
    exact (mul_le_iff_le_one_right (zpow_pos hpos _)).1 h
  · rw [Matrix.mul_add]
    refine hM _ _ fun i j => ?_
    show valuation k _ ≤ _
    rw [hval]
    refine (mul_le_mul_right (hy i j) _).trans_eq ?_
    rw [hϖ, ← zpow_natCast, ← zpow_add₀ hpos.ne']
    congr 1
    push_cast
    ring
end PositivityTheory.ThK.SplitLoc.Unr
