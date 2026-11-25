-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_inj_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:27.607819+00:00
-- url     : https://prove2.me/submissions/a41bea15-d41e-4195-b324-014da55ebb8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {O : Set (Fin e → ℂ)} {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (hO : IsOpen O) :
    ∃ W : ℕ → Set (Fin e → ℂ), (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ O) ∧ (∀ n, InjOn Q (W n)) ∧
      ⋃ n, W n = O := by
  classical
  set s : Set (Set (Fin e → ℂ)) :=
    insert ∅ {b | b ∈ TopologicalSpace.countableBasis (Fin e → ℂ) ∧ b ⊆ O ∧ InjOn Q b}
  have hs : s.Countable :=
    ((TopologicalSpace.countable_countableBasis _).mono fun b hb => hb.1).insert ∅
  have hmem : ∀ n, Set.enumerateCountable hs ∅ n ∈ s := Set.enumerateCountable_mem hs
    (Set.mem_insert _ _)
  refine ⟨Set.enumerateCountable hs ∅, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · rcases hmem n with h | h
    · rw [h]; exact isOpen_empty
    · exact TopologicalSpace.isOpen_of_mem_countableBasis h.1
  · rcases hmem n with h | h
    · rw [h]; exact empty_subset _
    · exact h.2.1
  · rcases hmem n with h | h
    · rw [h]; exact injOn_empty _
    · exact h.2.2
  · refine Subset.antisymm (iUnion_subset fun n => ?_) fun u hu => ?_
    · rcases hmem n with h | h
      · rw [h]; exact empty_subset _
      · exact h.2.1
    obtain ⟨hQa, hQd⟩ := hQ u hu
    set Ce := (fderiv ℂ Q u).toContinuousLinearEquivOfDetNeZero hQd
    have hCe : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ Q u :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hQd
    have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
      rw [hCe]; exact hQa.hasStrictFDerivAt
    set F := hstrict.toOpenPartialHomeomorph Q
    have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
    have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
    obtain ⟨b, hbB, hub, hbsub⟩ := (TopologicalSpace.isBasis_countableBasis (Fin e → ℂ)).exists_subset_of_mem_open
      (⟨hus, hu⟩ : u ∈ F.source ∩ O) (F.open_source.inter hO)
    have hbs : b ∈ s := Or.inr ⟨hbB, fun v hv => (hbsub hv).2, by
      rw [← hFc]; exact F.injOn.mono fun v hv => (hbsub hv).1⟩
    obtain ⟨n, hn⟩ := Set.subset_range_enumerate hs ∅ hbs
    exact mem_iUnion.mpr ⟨n, hn ▸ hub⟩
end ReciprocityTheory.ChartRestriction.G.Geo
