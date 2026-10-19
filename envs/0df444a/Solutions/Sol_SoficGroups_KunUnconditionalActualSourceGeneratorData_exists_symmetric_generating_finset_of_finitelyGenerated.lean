-- Prove2me | solution 1 for SoficGroups.KunUnconditionalActualSourceGeneratorData.exists_symmetric_generating_finset_of_finitelyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/0e47ea14-7bab-4e61-9f9e-62182bf08f75

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUnconditionalActualSourceGeneratorData
open SoficGroups.KunExactKazhdanGeneratorChange
open SoficGroups.KunExactActualSourceAmbientGenerators
namespace SoficGroups.KunUnconditionalActualSourceGeneratorData
theorem _root_.solution
    {G : Type*} [Group G]
    (hfg : Group.FG G) :
    ∃ S : Finset G,
      1 ∈ S ∧
        (∀ g ∈ S, g⁻¹ ∈ S) ∧
        Subgroup.closure (S : Set G) = ⊤ := by
  classical
  obtain ⟨_, T, _, hT⟩ := (Group.fg_iff').1 hfg
  let S : Finset G := insert 1 (T ∪ T.image fun g => g⁻¹)
  refine ⟨S, by simp [S], ?_, ?_⟩
  · intro g hg
    have hcases :
        g = 1 ∨ g ∈ T ∨
          ∃ y ∈ T, y⁻¹ = g := by
      simpa [S, Finset.mem_image] using hg
    rcases hcases with rfl | hgT | ⟨y, hy, rfl⟩
    · simp [S]
    · have hmem :
          g⁻¹ ∈ T.image fun z => z⁻¹ :=
        Finset.mem_image.mpr ⟨g, hgT, rfl⟩
      simp [S, hmem]
    · simp [S, hy]
  · have hsubset : (T : Set G) ⊆ (S : Set G) := by
      intro g hg
      change g ∈ T at hg
      change g ∈ S
      simp [S, hg]
    apply top_unique
    rw [← hT]
    exact Subgroup.closure_mono hsubset
end SoficGroups.KunUnconditionalActualSourceGeneratorData
