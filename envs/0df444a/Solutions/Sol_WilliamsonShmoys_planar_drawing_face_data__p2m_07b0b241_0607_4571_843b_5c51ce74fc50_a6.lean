-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_data__p2m_07b0b241_0607_4571_843b_5c51ce74fc50_a6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:29:58.983989+00:00
-- url     : https://prove2.me/submissions/3a670cc6-ee53-4175-82e5-f559dde42f9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_has_triangular_map_of_maximal_planar_drawing__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
import Theorems.Thm_WilliamsonShmoys_triangular_map_face_data__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∃ (m : Nat) (length : Fin m → Nat)
      (corner : ∀ f, Fin (length f) → V)
      (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart),
      (∀ f i, (dart ⟨f, i⟩).fst = corner f i) ∧
      (∀ f i, (dart ⟨f, i⟩).snd = corner f ⟨(i.val + 1) % length f, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) ∧
      H.Connected ∧
      (∀ f, 3 ≤ length f) ∧
      (∀ d e : H.Dart, d.fst = e.fst →
        ∃ k : Nat,
          (fun a : H.Dart =>
            dart ⟨(dart.symm a.symm).1,
              ⟨(((dart.symm a.symm).2).val + 1) % length ((dart.symm a.symm).1),
                Nat.mod_lt _ (Nat.zero_lt_of_lt ((dart.symm a.symm).2).isLt)⟩⟩)^[k] d = e) ∧
      m + Fintype.card V = H.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, length f) = 2 * H.edgeSet.ncard := by
  obtain ⟨F, instF, hM⟩ :=
    WilliamsonShmoys.has_triangular_map_of_maximal_planar_drawing__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
      H hH hV hconn hcount
  letI : Fintype F := instF
  obtain ⟨M⟩ := hM
  exact WilliamsonShmoys.triangular_map_face_data__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
    H hV hcount F M