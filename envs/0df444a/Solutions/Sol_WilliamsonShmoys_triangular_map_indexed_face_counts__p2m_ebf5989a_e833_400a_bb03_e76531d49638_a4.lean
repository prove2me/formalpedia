-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_indexed_face_counts__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:40:33.518582+00:00
-- url     : https://prove2.me/submissions/6190a7ca-f45c-46c0-9189-db8ddfd2f8b0

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (m : Nat) (length : Fin m → Nat)
    (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart)
    (hlength : ∀ f, length f = 3) :
    m + Fintype.card V = H.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, length f) = 2 * H.edgeSet.ncard := by
  classical
  have hedge : H.edgeFinset.card = H.edgeSet.ncard := by
    rw [H.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have hdarts : Fintype.card H.Dart = 2 * H.edgeSet.ncard := by
    calc
      Fintype.card H.Dart = 2 * H.edgeFinset.card := H.dart_card_eq_twice_card_edges
      _ = 2 * H.edgeSet.ncard := by rw [hedge]
  have hsum : (∑ f : Fin m, length f) = 2 * H.edgeSet.ncard := by
    calc
      (∑ f : Fin m, length f) = Fintype.card (Σ f : Fin m, Fin (length f)) := by
        simp
      _ = Fintype.card H.Dart := Fintype.card_congr dart
      _ = 2 * H.edgeSet.ncard := hdarts
  have hsumlen : (∑ f : Fin m, length f) = m * 3 := by
    simp [hlength]
  have hthree : 3 * m = 2 * H.edgeSet.ncard := by
    calc
      3 * m = m * 3 := Nat.mul_comm _ _
      _ = ∑ f : Fin m, length f := hsumlen.symm
      _ = 2 * H.edgeSet.ncard := hsum
  constructor
  · omega
  · exact hsum