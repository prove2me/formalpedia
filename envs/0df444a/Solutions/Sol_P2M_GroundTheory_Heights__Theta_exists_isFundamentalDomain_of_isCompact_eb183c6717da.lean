-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_exists_isFundamentalDomain_of_isCompact_eb183c6717da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:17.836783+00:00
-- url     : https://prove2.me/submissions/9ba4a7e3-3ac2-4da3-9cf2-03879bf161c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_isOpen_small_b5c2f2fc479e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_measurableSet_firstHit_3bd575bb091f
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_existsUnique_mem_firstHit_2887f9ddb304

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {C : Set G} (hC : IsCompact C)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ C) :
    ∃ 𝓕 L : Set G, MeasurableSet 𝓕 ∧ IsCompact L ∧ 𝓕 ⊆ L ∧ ∀ x, ∃! γ : Γ, γ • x ∈ 𝓕 := by
  classical
  choose V hVo hcV hVL hVinj using exists_isOpen_small Γ
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hVo (fun c _ => mem_iUnion.mpr ⟨c, hcV c⟩)
  let l := t.toList
  let A : ℕ → Set G := fun i => if h : i < l.length then V (l.get ⟨i, h⟩) else ∅
  have hAo : ∀ i, IsOpen (A i) := fun i => by
    simp only [A]; split_ifs
    · exact hVo _
    · exact isOpen_empty
  have hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1 := by
    intro i γ hγ x hx hγx
    simp only [A] at hx hγx
    split_ifs at hx hγx with h
    · exact hVinj _ γ hγ x hx hγx
    · exact hx.elim
  have hcovA : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i := by
    intro x
    obtain ⟨γ, hγ, hγC⟩ := hcov x
    obtain ⟨c, hc⟩ := mem_iUnion.mp (ht hγC)
    obtain ⟨hct, hcV'⟩ := mem_iUnion.mp hc
    obtain ⟨n, hn, hnc⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hct)
    refine ⟨n, γ, hγ, ?_⟩
    show γ * x ∈ (if h : n < l.length then V (l.get ⟨n, h⟩) else ∅)
    rw [dif_pos hn]
    have hget : l.get ⟨n, hn⟩ = c := hnc
    rw [hget]
    exact hcV'
  choose L hL hVL' using hVL
  refine ⟨firstHit Γ A, ⋃ c ∈ t, L c, measurableSet_firstHit Γ hAo,
    t.isCompact_biUnion fun c _ => hL c, ?_, existsUnique_mem_firstHit Γ A hinj hcovA⟩
  intro y hy
  obtain ⟨i, hi, -⟩ := mem_iUnion.mp hy
  simp only [A] at hi
  split_ifs at hi with h
  · exact mem_iUnion₂.mpr ⟨l.get ⟨i, h⟩, Finset.mem_toList.mp (List.get_mem l _), hVL' _ hi⟩
  · exact hi.elim
end GroundTheory.Heights₂.Theta
