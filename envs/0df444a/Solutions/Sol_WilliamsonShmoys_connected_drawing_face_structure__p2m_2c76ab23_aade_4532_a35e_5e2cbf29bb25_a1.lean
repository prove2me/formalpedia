-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_face_structure__p2m_2c76ab23_aade_4532_a35e_5e2cbf29bb25_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:51:01.964861+00:00
-- url     : https://prove2.me/submissions/096e5770-041f-428c-95fb-3bbf50d95283

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_face_structure_core__p2m_49320d7c_d315_47bf_bd18_a40df71c3333_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (hcard : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (F : Type) (hF : Fintype F) (hFdec : DecidableEq F) (face : K.Dart → F),
      (letI : Fintype F := hF
       letI : DecidableEq F := hFdec
       Fintype.card V + Fintype.card F = K.edgeFinset.card + 2 ∧
       (∀ f : F, 3 ≤ Fintype.card {d : K.Dart // face d = f}) ∧
       (∑ f : F, Fintype.card {d : K.Dart // face d = f}) = Fintype.card K.Dart) := by
  classical
  obtain ⟨F, hF, hFdec, face, hcore⟩ :=
    WilliamsonShmoys.connected_drawing_face_structure_core__p2m_49320d7c_d315_47bf_bd18_a40df71c3333_a2
      K hcard hconn hK
  letI : Fintype F := hF
  letI : DecidableEq F := hFdec
  refine ⟨F, hF, hFdec, face, ?_⟩
  refine ⟨hcore.1, hcore.2, ?_⟩
  let e : (Σ f : F, {d : K.Dart // face d = f}) ≃ K.Dart :=
    { toFun := fun x => x.2.1
      invFun := fun d => ⟨face d, ⟨d, rfl⟩⟩
      left_inv := by
        rintro ⟨f, ⟨d, hd⟩⟩
        cases hd
        rfl
      right_inv := by
        intro d
        rfl }
  simpa using Fintype.card_congr e