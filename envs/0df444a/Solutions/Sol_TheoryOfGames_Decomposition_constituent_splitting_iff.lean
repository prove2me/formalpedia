-- Prove2me | solution 1 for TheoryOfGames.Decomposition.constituent_splitting_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:30:17.804268+00:00
-- url     : https://prove2.me/submissions/6a04c1c1-30d1-49fc-a605-8decf1971691

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting
import Definitions.Def_TheoryOfGames_Decomposition_Constituent

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) (hJ : IsSplitting v J)
    (J' : Finset J) :
    IsSplitting (constituent v J) J' ↔
      IsSplitting v (J'.map (Function.Embedding.subtype (· ∈ J))) := by
  constructor
  · intro h S T hS hT
    -- pull back S and T ∩ J to the subtype
    have hSJ : ∀ x ∈ S, x ∈ J := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 (hS hx)
      exact y.2
    set T1 := T.filter (· ∈ J) with hT1
    set T2 := T.filter (· ∉ J) with hT2
    have hT12 : T = T1 ∪ T2 := by
      rw [hT1, hT2, Finset.filter_union_filter_not_eq]
    have hT1J : ∀ x ∈ T1, x ∈ J := fun x hx => (Finset.mem_filter.1 hx).2
    have hT2J : T2 ⊆ Jᶜ := by
      intro x hx
      simpa using (Finset.mem_filter.1 hx).2
    have hS' : (S.subtype (· ∈ J)).map (Function.Embedding.subtype (· ∈ J)) = S :=
      Finset.subtype_map_of_mem hSJ
    have hT1' : (T1.subtype (· ∈ J)).map (Function.Embedding.subtype (· ∈ J)) = T1 :=
      Finset.subtype_map_of_mem hT1J
    have key : v (S ∪ T1) = v S + v T1 := by
      have := h (S.subtype (· ∈ J)) (T1.subtype (· ∈ J)) ?_ ?_
      · simpa [constituent, Finset.map_union, hS', hT1'] using this
      · intro x hx
        rw [Finset.mem_subtype] at hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_map.1 (hS hx)
        have : y = x := Subtype.ext hyx
        rw [← this]; exact hy
      · intro x hx
        rw [Finset.mem_subtype] at hx
        rw [Finset.mem_compl]
        intro hxJ
        have hxT : (x : ι) ∈ T := (Finset.mem_filter.1 hx).1
        have := hT hxT
        rw [Finset.mem_compl] at this
        exact this (Finset.mem_map.2 ⟨x, hxJ, rfl⟩)
    have hST1J : S ∪ T1 ⊆ J := by
      intro x hx
      rcases Finset.mem_union.1 hx with h1 | h1
      · exact hSJ x h1
      · exact hT1J x h1
    have e1 : v ((S ∪ T1) ∪ T2) = v (S ∪ T1) + v T2 := hJ _ _ hST1J hT2J
    have e2 : v (T1 ∪ T2) = v T1 + v T2 := hJ _ _ (fun x hx => hT1J x hx) hT2J
    rw [hT12, ← Finset.union_assoc, e1, key, e2]
    ring
  · intro h S T hS hT
    show v ((S ∪ T).map _) = v (S.map _) + v (T.map _)
    rw [Finset.map_union]
    apply h
    · exact Finset.map_subset_map.2 hS
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
      rw [Finset.mem_compl]
      intro hm
      obtain ⟨z, hz, hzy⟩ := Finset.mem_map.1 hm
      have : z = y := Subtype.ext hzy
      subst this
      exact (Finset.mem_compl.1 (hT hy)) hz
