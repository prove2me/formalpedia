-- Prove2me | solution 1 for TheoryOfGames.Decomposition.partition_univ_iff_indecomposable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:11:05.721983+00:00
-- url     : https://prove2.me/submissions/50bad80a-f36d-4016-8b64-cfdf105b374f

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem fec73891_exists_minimal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J : Finset ι) :
    IsSplitting v J → J.Nonempty → ∃ J' ⊆ J, IsMinimalSplitting v J' := by
  induction J using Finset.strongInduction with
  | H J ih =>
    intro hs hne
    by_cases hmin : ∀ J' : Finset ι, IsSplitting v J' → J'.Nonempty → J' ⊆ J → J' = J
    · exact ⟨J, subset_rfl, hs, hne, hmin⟩
    · push_neg at hmin
      obtain ⟨J', hs', hne', hsub, hne2⟩ := hmin
      have hss : J' ⊂ J := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne2⟩
      obtain ⟨K, hK, hKmin⟩ := ih J' hss hs' hne'
      exact ⟨K, hK.trans hsub, hKmin⟩

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    decompositionPartition v = {Finset.univ} ↔ IsIndecomposable v := by
  constructor
  · intro h J hs
    by_cases hJ : J = ∅
    · exact Or.inl hJ
    · right
      have hne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
      obtain ⟨K, hK, hKmin⟩ := fec73891_exists_minimal v J hs hne
      have hmem : K ∈ decompositionPartition v := hKmin
      rw [h] at hmem
      have hKu : K = Finset.univ := hmem
      rw [hKu] at hK
      exact Finset.eq_univ_of_forall (fun x => hK (Finset.mem_univ x))
  · intro h
    ext J
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hJ
      obtain ⟨hs, hne, _⟩ := hJ
      rcases h J hs with h1 | h1
      · exact absurd h1 (Finset.nonempty_iff_ne_empty.mp hne)
      · exact h1
    · intro hJ
      subst hJ
      refine ⟨?_, Finset.univ_nonempty, ?_⟩
      · intro S T _ hT
        rw [Finset.compl_univ, Finset.subset_empty] at hT
        subst hT
        rw [Finset.union_empty, hv.empty, add_zero]
      · intro J' hs' hne' _
        rcases h J' hs' with h1 | h1
        · exact absurd h1 (Finset.nonempty_iff_ne_empty.mp hne')
        · exact h1
