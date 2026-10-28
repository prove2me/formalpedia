-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_certificate_cd4931de_38bf_49be_8f7a_54b333eaee7b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:45:28.868573+00:00
-- url     : https://prove2.me/submissions/51218e63-ad83-4441-b909-4002c312bdcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_MaximalPlanarEulerCertificate
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_count_for_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_incidence_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hWX : forall u v, W.Adj u v -> X.Adj u v)
    (hmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, W.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    HasMaximalPlanarEulerCertificate X := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_has_euler_face_count_for_maximal_supergraph
      W X hX hWX hmax hCard
  have hInc :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangular_incidence_count
      W X hX hWX hmax hCard f hEuler
  exact ⟨f, hEuler, hInc⟩