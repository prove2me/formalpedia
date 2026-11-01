-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:30.995115+00:00
-- url     : https://prove2.me/submissions/387898f9-1d55-455a-9135-b2744fc9f37e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (A B : SimpleGraph V) (dA : DecidableRel A.Adj) (dB : DecidableRel B.Adj)
    (hAB : (letI : DecidableRel A.Adj := dA
            letI : DecidableRel B.Adj := dB
            A.edgeFinset ⊆ B.edgeFinset))
    (hB : HasPlanarDrawingOn B) : HasPlanarDrawingOn A := by
  classical
  letI : DecidableRel A.Adj := dA
  letI : DecidableRel B.Adj := dB
  have hle : A ≤ B := SimpleGraph.edgeFinset_subset_edgeFinset.mp hAB
  rcases hB with ⟨p, arc, hp, hcurves, hdisjoint⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hA
    exact hcurves u v huv (hle hA)
  · intro u v x y huv hxy hAuv hAxy hneq t ht s hs heq
    exact hdisjoint u v x y huv hxy (hle hAuv) (hle hAxy) hneq t ht s hs heq