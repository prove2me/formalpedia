-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_of_predicate__p2m_96980b1a_9f95_4fab_928b_4c57cef78d59_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:53.536302+00:00
-- url     : https://prove2.me/submissions/f12fade6-4b46-4041-9469-6fddee4ae9aa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Finite.Lemmas

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (L : SimpleGraph V)
    (hL : P L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        P N →
        N = M := by
  classical
  let S : Set (SimpleGraph V) := {G | P G ∧ L ≤ G}
  have hSfinite : S.Finite := Set.toFinite S
  obtain ⟨M, hM, hmax⟩ :=
    Set.exists_max_image S (fun G : SimpleGraph V => #G.edgeFinset) hSfinite
      ⟨L, hL, le_rfl⟩
  refine ⟨M, ?_, hM.1, ?_⟩
  · exact SimpleGraph.edgeSet_subset_edgeSet.mpr hM.2
  · intro N hMN hPN
    have hNM : M ≤ N := SimpleGraph.edgeSet_subset_edgeSet.mp hMN
    have hNmem : N ∈ S := ⟨hPN, hM.2.trans hNM⟩
    have hcard : #N.edgeFinset ≤ #M.edgeFinset := hmax N hNmem
    have hsubset : M.edgeFinset ⊆ N.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hNM
    have heq : M.edgeFinset = N.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsubset hcard
    exact (SimpleGraph.edgeFinset_inj.mp heq).symm