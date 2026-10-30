-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_face_data__p2m_8b018285_4ad7_4c76_beb1_fed47f71a69b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:28:50.013234+00:00
-- url     : https://prove2.me/submissions/90385693-2a4f-4d56-98dd-a8654ffe09c4

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_triangular_map_indexed_face_data__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
import Theorems.Thm_WilliamsonShmoys_triangular_map_indexed_face_counts__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (F : Type) [Fintype F]
    (M : WilliamsonShmoys.TriangularMap H F) :
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
  rcases WilliamsonShmoys.triangular_map_indexed_face_data__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
      H F M with
    ⟨m, length, corner, dart, hlength, htail, hhead, hinjective, hcovered, hconnected, hrotation⟩
  rcases WilliamsonShmoys.triangular_map_indexed_face_counts__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
      H hcount m length dart hlength with ⟨heuler, htotal⟩
  refine ⟨m, length, corner, dart, htail, hhead, hinjective, hcovered, hconnected, ?_, hrotation, heuler, htotal⟩
  intro f
  rw [hlength f]