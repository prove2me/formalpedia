-- Prove2me | solution 1 for TheoryOfGames.Decomposition.constituent_indecomposable_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:57:06.276133+00:00
-- url     : https://prove2.me/submissions/4da09ff7-3e87-4476-8f00-594f438d1c89

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting
import Definitions.Def_TheoryOfGames_Decomposition_Constituent

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem P2M2d853489_map_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J X : Finset ι) (hX : X ⊆ J) :
    (X.subtype (· ∈ J)).map (Function.Embedding.subtype (· ∈ J)) = X :=
  Finset.subtype_map_of_mem (fun _x hx => hX hx)

open TheoryOfGames.Decomposition in
theorem P2M2d853489_toDelta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J : Finset ι) (A : Finset J)
    (h : IsSplitting v (A.map (Function.Embedding.subtype (· ∈ J)))) :
    IsSplitting (constituent v J) A := by
  intro S T hS hT
  unfold constituent
  rw [Finset.map_union]
  apply h
  · exact Finset.map_subset_map.mpr hS
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Finset.mem_compl, Finset.mem_map']
    have := hT hy
    rwa [Finset.mem_compl] at this

open TheoryOfGames.Decomposition in
theorem P2M2d853489_ofDelta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J : Finset ι) (hJ : IsSplitting v J) (A : Finset J)
    (h : IsSplitting (constituent v J) A) :
    IsSplitting v (A.map (Function.Embedding.subtype (· ∈ J))) := by
  intro S T hS hT
  have hAJ : A.map (Function.Embedding.subtype (· ∈ J)) ⊆ J := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  have hSJ : S ⊆ J := hS.trans hAJ
  have hT1J : T ∩ J ⊆ J := Finset.inter_subset_right
  have hT2 : T \ J ⊆ Jᶜ := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    exact Finset.mem_compl.mpr hx.2
  have hTsplit : T = (T ∩ J) ∪ (T \ J) := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  -- Δ-splitting applied to S' and T1'
  have hΔ := h (S.subtype (· ∈ J)) ((T ∩ J).subtype (· ∈ J)) ?_ ?_
  · unfold constituent at hΔ
    rw [Finset.map_union, P2M2d853489_map_sub J S hSJ,
      P2M2d853489_map_sub J (T ∩ J) hT1J] at hΔ
    have hSU : S ∪ (T ∩ J) ⊆ J := Finset.union_subset hSJ hT1J
    have e1 : v (S ∪ T) = v ((S ∪ (T ∩ J)) ∪ (T \ J)) := by
      congr 1
      conv_lhs => rw [hTsplit]
      rw [Finset.union_assoc]
    have e2 := hJ (S ∪ (T ∩ J)) (T \ J) hSU hT2
    have e3 := hJ (T ∩ J) (T \ J) hT1J hT2
    rw [← hTsplit] at e3
    rw [e1, e2, hΔ, e3]
    ring
  · intro y hy
    rw [Finset.mem_subtype] at hy
    have := hS hy
    rw [Finset.mem_map] at this
    obtain ⟨z, hz, hzy⟩ := this
    have : z = y := Subtype.ext hzy
    rwa [← this]
  · intro y hy
    rw [Finset.mem_subtype, Finset.mem_inter] at hy
    rw [Finset.mem_compl]
    intro hyA
    have := hT hy.1
    rw [Finset.mem_compl] at this
    exact this (Finset.mem_map_of_mem _ hyA)

-- (43:E), 43.3.2: the J-constituent is indecomposable iff J is a minimal splitting set.
open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) (hJ : IsSplitting v J)
    (hJne : J.Nonempty) :
    IsIndecomposable (constituent v J) ↔ IsMinimalSplitting v J := by
  constructor
  · intro hind
    refine ⟨hJ, hJne, fun J' hJ' hne hsub => ?_⟩
    have hm := P2M2d853489_map_sub J J' hsub
    rw [← hm] at hJ'
    rcases hind _ (P2M2d853489_toDelta v J _ hJ') with h0 | h1
    · rw [h0, Finset.map_empty] at hm
      rw [← hm] at hne
      exact absurd hne Finset.not_nonempty_empty
    · rw [h1] at hm
      rw [← hm]
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨_, _, hmin⟩ A hA
    by_cases h0 : A = ∅
    · exact Or.inl h0
    · right
      have hne : (A.map (Function.Embedding.subtype (· ∈ J))).Nonempty := by
        rw [Finset.map_nonempty]
        exact Finset.nonempty_iff_ne_empty.mpr h0
      have hsub : A.map (Function.Embedding.subtype (· ∈ J)) ⊆ J := by
        intro x hx
        rw [Finset.mem_map] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact y.2
      have heq := hmin _ (P2M2d853489_ofDelta v J hJ A hA) hne hsub
      ext y
      simp only [Finset.mem_univ, iff_true]
      have hy : (y : ι) ∈ A.map (Function.Embedding.subtype (· ∈ J)) := by
        rw [heq]; exact y.2
      exact (Finset.mem_map' _).mp hy
