-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_extension__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:58.579886+00:00
-- url     : https://prove2.me/submissions/2fcf9147-13f9-444f-aa02-d15a6aca8bde

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Finite
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q := by
  classical
  let S : Set (SimpleGraph V) := {Q | P ≤ Q ∧ HasPlanarDrawingOn Q}
  have hS : S.Finite := Set.toFinite S
  have hSn : S.Nonempty := ⟨P, le_rfl, hDraw⟩
  obtain ⟨Q, hQ, hmax⟩ :=
    Set.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hS hSn
  refine ⟨Q, hQ.1, hQ.2, ?_⟩
  intro R hQR hR
  have hRmem : R ∈ S := ⟨hQ.1.trans hQR, hR⟩
  have hcard : R.edgeFinset.card ≤ Q.edgeFinset.card := hmax R hRmem
  have hedges : Q.edgeFinset = R.edgeFinset :=
    Finset.eq_of_subset_of_card_le
      (SimpleGraph.edgeFinset_subset_edgeFinset.mpr hQR) hcard
  have heq : Q = R := SimpleGraph.edgeFinset_inj.mp hedges
  exact le_of_eq heq.symm