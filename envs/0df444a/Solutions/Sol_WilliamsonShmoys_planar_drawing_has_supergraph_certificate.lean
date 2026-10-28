-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_supergraph_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:16:00.203756+00:00
-- url     : https://prove2.me/submissions/660d2feb-f64a-4733-afb3-edcf10a68624
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_cd4931de_38bf_49be_8f7a_54b333eaee7b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_certificate_cd4931de_38bf_49be_8f7a_54b333eaee7b

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V,
      HasPlanarDrawingOn X ∧
      (∀ u v, W.Adj u v → X.Adj u v) ∧
      HasMaximalPlanarEulerCertificate X := by
  obtain ⟨X, hX, hWX, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_cd4931de_38bf_49be_8f7a_54b333eaee7b W hW
  exact ⟨X, hX, hWX,
    WilliamsonShmoys.maximal_planar_drawing_has_euler_certificate_cd4931de_38bf_49be_8f7a_54b333eaee7b
      W X hX hWX hmax hCard⟩