-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:50:32.534983+00:00
-- url     : https://prove2.me/submissions/e36efe19-ee83-4021-bd40-fa2b6f089f13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_supergraph_certificate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, HasPlanarDrawingOn X →
      (∀ u v, W.Adj u v → X.Adj u v) →
      ∀ u v, X.Adj u v → W.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    HasMaximalPlanarEulerCertificate W := by
  obtain ⟨X, hX, hWX, hcert⟩ :=
    WilliamsonShmoys.planar_drawing_has_supergraph_certificate W hW hCard
  have hXW : ∀ u v, X.Adj u v → W.Adj u v := hmax X hX hWX
  have hEq : W = X := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    exact ⟨hWX u v, hXW u v⟩
  simpa [hEq] using hcert