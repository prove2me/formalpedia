-- Prove2me | solution 1 for TheoryOfGames.Decomposition.partition_singletons_iff_inessential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:18:46.907639+00:00
-- url     : https://prove2.me/submissions/6933c51c-5394-429f-a4f8-60574b319a33

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem a85bab99_additive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (h0 : v ∅ = 0) (hs : ∀ k : ι, IsSplitting v {k}) :
    ∀ S : Finset ι, v S = ∑ k ∈ S, v {k} := by
  intro S
  induction S using Finset.induction_on with
  | empty => simp [h0]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.insert_eq]
    apply hs a {a} S (Finset.Subset.refl _)
    intro x hx
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    exact ha hx

open TheoryOfGames.Decomposition in
theorem a85bab99_split_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (α₀ : ι → ℝ) (hα : ∀ S : Finset ι, v S + ∑ k ∈ S, α₀ k = 0)
    (J : Finset ι) : IsSplitting v J := by
  intro S T hS hT
  have hd : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    exact (Finset.mem_compl.mp (hT hxT)) (hS hxS)
  have h1 := hα (S ∪ T)
  have h2 := hα S
  have h3 := hα T
  rw [Finset.sum_union hd] at h1
  linarith

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    decompositionPartition v = {J : Finset ι | ∃ k : ι, J = {k}} ↔ IsInessential v := by
  constructor
  · intro h
    have hs : ∀ k : ι, IsSplitting v {k} := by
      intro k
      have hk : ({k} : Finset ι) ∈ decompositionPartition v := by
        rw [h]; exact ⟨k, rfl⟩
      exact hk.1
    refine ⟨fun k => - v {k}, fun S => ?_⟩
    rw [a85bab99_additive v hv.empty hs S, Finset.sum_neg_distrib]
    ring
  · rintro ⟨α₀, hα⟩
    ext J
    simp only [decompositionPartition, IsMinimalSplitting, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨k, hk⟩, hmin⟩
      refine ⟨k, ?_⟩
      exact (hmin {k} (a85bab99_split_all v α₀ hα _) (Finset.singleton_nonempty k)
        (Finset.singleton_subset_iff.mpr hk)).symm
    · rintro ⟨k, rfl⟩
      refine ⟨a85bab99_split_all v α₀ hα _, Finset.singleton_nonempty k, ?_⟩
      intro J' _ hne hsub
      exact (Finset.Nonempty.subset_singleton_iff hne).mp hsub
