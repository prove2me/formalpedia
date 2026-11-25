-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTransgression.exists_cont_select
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:07.863966+00:00
-- url     : https://prove2.me/submissions/d839e105-2440-4097-9223-a3786eee10c8

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.InflationTransgression
theorem _root_.solution {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {Y : Type u} [TopologicalSpace Y] [DiscreteTopology Y] [Nonempty Y]
    (P : X → Y → Prop) (hP : ∀ y, IsOpen {x | P x y}) (hex : ∀ x, ∃ y, P x y) :
    ∃ ψ : X → Y, Continuous ψ ∧ ∀ x, P x (ψ x) := by
  classical
  have hb : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} := by
    first
      | exact isTopologicalBasis_isClopen
      | exact isTopologicalBasis_clopen
  choose yx hyx using hex
  have hnb : ∀ x, ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ C ⊆ {x' | P x' (yx x)} := by
    intro x
    obtain ⟨C, hC, hxC, hCs⟩ := hb.exists_subset_of_mem_open (hyx x) (hP (yx x))
    exact ⟨C, hC, hxC, hCs⟩
  choose C hCc hxC hCs using hnb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover C (fun x => (hCc x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxC x⟩)
  have key : ∀ s : Finset X, ∃ ψ : X → Y, Continuous ψ ∧ ∀ x ∈ s, ∀ z ∈ C x, P z (ψ z) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨fun _ => Classical.arbitrary Y, continuous_const, by simp⟩
    · intro a s _ ih
      obtain ⟨ψ, hψc, hψ⟩ := ih
      refine ⟨fun z => if z ∈ C a then yx a else ψ z, ?_, ?_⟩
      · apply continuous_if
        · intro x hx
          have hfr : frontier {x | x ∈ C a} = ∅ := (hCc a).frontier_eq
          rw [hfr] at hx
          simp at hx
        · exact continuous_const.continuousOn
        · exact hψc.continuousOn
      · intro x hx z hz
        by_cases hza : z ∈ C a
        · dsimp only
          rw [if_pos hza]
          exact hCs a hza
        · dsimp only
          rw [if_neg hza]
          rcases Finset.mem_insert.1 hx with rfl | hx'
          · exact absurd hz hza
          · exact hψ x hx' z hz
  obtain ⟨ψ, hψc, hψ⟩ := key t
  refine ⟨ψ, hψc, fun z => ?_⟩
  obtain ⟨x, hx, hz⟩ : ∃ x ∈ t, z ∈ C x := by simpa using ht (Set.mem_univ z)
  exact hψ x hx z hz
end ReciprocityTheory.Coh.InflationTransgression
