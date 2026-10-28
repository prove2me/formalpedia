-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_repair
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:43:35.087849+00:00
-- url     : https://prove2.me/submissions/7e27798b-b48c-4b65-bf69-00dd5e58676b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T := by
  classical
  let S : Set (SimpleGraph V) := {T | L ≤ T ∧ HasPlanarDrawingOn T}
  have hS : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨T, hT⟩ := hS.exists_maximal hSne
  have hmem : T ∈ S := hT.1
  rcases hmem with ⟨hLT, hdrawT⟩
  refine ⟨T, hLT, hdrawT, ?_⟩
  intro U hTU hdrawU
  have hUmem : U ∈ S := ⟨hLT.trans hTU, hdrawU⟩
  have hUT : U ≤ T := hT.2 hUmem hTU
  exact le_antisymm hUT hTU