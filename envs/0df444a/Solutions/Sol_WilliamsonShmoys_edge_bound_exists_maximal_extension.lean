-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_exists_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:28:15.363807+00:00
-- url     : https://prove2.me/submissions/5fe6bb67-967c-4a84-9b26-42815a9cc734

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H := by
  classical
  let P : SimpleGraph V → Prop := fun G => K ≤ G ∧ HasPlanarDrawingOn G
  let Q : Set Nat := {n | ∃ G : SimpleGraph V, P G ∧ G.edgeFinset.card = n}
  have hPK : P K := ⟨le_rfl, hDraw⟩
  have hQK : K.edgeFinset.card ∈ Q := ⟨K, hPK, rfl⟩
  have hQbounded : Q ⊆ Set.Iic (⊤ : SimpleGraph V).edgeFinset.card := by
    intro n hn
    rcases hn with ⟨G, hG, rfl⟩
    exact Finset.card_le_card
      (SimpleGraph.edgeFinset_subset_edgeFinset.mpr (le_top : G ≤ ⊤))
  have hQfinite : Q.Finite := (Set.finite_Iic _).subset hQbounded
  obtain ⟨n, hnQ, hmax⟩ :=
    Set.exists_max_image Q id hQfinite ⟨K.edgeFinset.card, hQK⟩
  rcases hnQ with ⟨H, hH, hcard⟩
  have hKH : K ≤ H := hH.1
  have hHDraw : HasPlanarDrawingOn H := hH.2
  refine ⟨H, hKH, hHDraw, ?_⟩
  intro J hHJ hJDraw
  have hKJ : K ≤ J := le_trans hKH hHJ
  have hJQ : J.edgeFinset.card ∈ Q := ⟨J, ⟨hKJ, hJDraw⟩, rfl⟩
  have hcard_le : J.edgeFinset.card ≤ H.edgeFinset.card := by
    simpa [hcard] using hmax J.edgeFinset.card hJQ
  have heq : H.edgeFinset = J.edgeFinset :=
    Finset.eq_of_subset_of_card_le
      (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hHJ)
      hcard_le
  exact (SimpleGraph.edgeFinset_inj.mp heq).symm
