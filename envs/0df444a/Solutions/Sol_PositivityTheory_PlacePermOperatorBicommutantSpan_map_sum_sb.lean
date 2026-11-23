-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.map_sum_sb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:29.141804+00:00
-- url     : https://prove2.me/submissions/52bbc6f2-0398-4aba-8abf-c5a694c292f5

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_smul
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_zero
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
omit h [AddCommGroup V] [MeasurableSpace V]
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) {α : Type} (s : Finset α) (c : α → ℂ) {f : α → V → ℂ}
    (hf : ∀ a, SB (f a)) : T (∑ a ∈ s, c a • f a) = ∑ a ∈ s, c a • T (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hsm 0 0 sb_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ (sb_smul _ (hf a)) (sb_sum _ fun b _ => sb_smul _ (hf b)),
      hsm _ _ (hf a), ih]
end PositivityTheory.PlacePermOperatorBicommutantSpan
