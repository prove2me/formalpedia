-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:37.93906+00:00
-- url     : https://prove2.me/submissions/f8ae7702-a615-401f-8c51-35874a4b7e50

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_CO_inf
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_isOpen_coset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_co_cpt

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
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (h : NADual V χ μ) {φ : V → ℂ} (hφ : SB φ) :
    ∃ L L' : AddSubgroup V, CO L ∧ CO L' ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  obtain ⟨L, hL, hKL⟩ := co_cpt h hφ.2.isCompact
  obtain ⟨_, -, -, -, -, -, hsmall, -⟩ := h
  have h0 : ∀ x, x ∉ L → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h' => hx (hKL h')
  have key : ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ (L : Set V), ∀ l ∈ L', φ (x + l) = φ x := by
    refine hL.1.induction_on
      (p := fun s => ∃ L' : AddSubgroup V, IsOpen (L' : Set V) ∧ ∀ x ∈ s, ∀ l ∈ L', φ (x + l) = φ x) ?_ ?_ ?_ ?_
    · exact ⟨⊤, isOpen_univ, fun _ h => absurd h (notMem_empty _)⟩
    · rintro s t hst ⟨L', h1, h2⟩
      exact ⟨L', h1, fun x hx => h2 x (hst hx)⟩
    · rintro s t ⟨L₁, h1, h2⟩ ⟨L₂, h1', h2'⟩
      exact ⟨L₁ ⊓ L₂, h1.inter h1', fun x hx l hl => hx.elim (fun h => h2 x h l hl.1) fun h => h2' x h l hl.2⟩
    · intro x _
      have hU : {y | φ (x + y) = φ x} ∈ 𝓝 (0 : V) := by
        have h1 : ContinuousAt (fun y => x + y) 0 := (continuous_const.add continuous_id).continuousAt
        exact h1.preimage_mem_nhds (by rw [add_zero]; exact hφ.1.eventually_eq x)
      obtain ⟨L₀, -, h2, h3⟩ := hsmall _ hU
      refine ⟨{y | y - x ∈ L₀}, mem_nhdsWithin_of_mem_nhds ((isOpen_coset x h2).mem_nhds (by simp)), L₀, h2,
        fun y hy l hl => ?_⟩
      have e1 : φ (x + (y - x + l)) = φ x := h3 (L₀.add_mem hy hl)
      have e2 : φ (x + (y - x)) = φ x := h3 hy
      rw [add_sub_cancel] at e2
      rw [← add_assoc, add_sub_cancel] at e1
      rw [e1, e2]
  obtain ⟨L', h1, h2⟩ := key
  refine ⟨L, L ⊓ L', hL, hL.inf h1, inf_le_left, h0, fun x l hl => ?_⟩
  by_cases hx : x ∈ L
  · exact h2 x hx l hl.2
  · rw [h0 x hx, h0 _ fun h' => hx ((L.add_mem_cancel_right hl.1).1 h')]
end PositivityTheory.PlacePermOperatorBicommutantSpan
