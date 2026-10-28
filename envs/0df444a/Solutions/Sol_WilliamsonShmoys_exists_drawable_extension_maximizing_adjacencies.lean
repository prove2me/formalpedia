-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_extension_maximizing_adjacencies
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:09:14.236349+00:00
-- url     : https://prove2.me/submissions/17aa58f3-9085-4549-9813-b545808fba8c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      And (LE.le N K) (And (HasPlanarDrawingOn K)
        (forall L : SimpleGraph V, LE.le N L -> HasPlanarDrawingOn L ->
          Nat.card {p : V × V // L.Adj p.1 p.2} <=
            Nat.card {p : V × V // K.Adj p.1 p.2})) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => LE.le N G ∧ HasPlanarDrawingOn G
  have hN : N ∈ candidates := by
    simp [candidates, hNdraw]
  obtain ⟨K, hK, hKmax⟩ :=
    Finset.exists_max_image candidates
      (fun G => Nat.card {p : V × V // G.Adj p.1 p.2})
      ⟨N, hN⟩
  have hK' : LE.le N K ∧ HasPlanarDrawingOn K := by
    simpa [candidates] using hK
  refine ⟨K, hK'.1, hK'.2, ?_⟩
  intro L hNL hLdraw
  apply hKmax
  simp [candidates, hNL, hLdraw]