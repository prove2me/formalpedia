-- Prove2me | solution 1 for WilliamsonShmoys.euler_certificate_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:33:09.521525+00:00
-- url     : https://prove2.me/submissions/130409a3-e4ad-43f1-bba7-51d0d47ca2ad

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hcert : HasMaximalPlanarEulerCertificate W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  rcases hcert with ⟨f, heuler, htri⟩
  omega