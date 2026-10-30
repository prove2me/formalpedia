-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_a35190bf_fe1a_4d87_ab3a_82a6067f7e12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:03.641504+00:00
-- url     : https://prove2.me/submissions/84c2dde5-de67-4732-bebf-0445e37ed74f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by
  classical
  let p : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  letI : Nonempty {G : SimpleGraph V // p G} :=
    ⟨⟨K, ⟨le_rfl, hK⟩⟩⟩
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image Finset.univ
      (fun x : {G : SimpleGraph V // p G} => x.val.edgeFinset.card)
      Finset.univ_nonempty
  refine ⟨x.val, x.property.1, x.property.2, ?_⟩
  intro M hLM hM
  have hMcandidate : p M := ⟨le_trans x.property.1 hLM, hM⟩
  have hcard : M.edgeFinset.card ≤ x.val.edgeFinset.card :=
    hmax ⟨M, hMcandidate⟩ (Finset.mem_univ _)
  have hedge : x.val.edgeFinset ⊆ M.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hLM
  have heq : x.val.edgeFinset = M.edgeFinset :=
    Finset.eq_of_subset_of_card_le hedge hcard
  have hgraph : x.val = M := SimpleGraph.edgeFinset_inj.mp heq
  exact le_of_eq hgraph.symm
