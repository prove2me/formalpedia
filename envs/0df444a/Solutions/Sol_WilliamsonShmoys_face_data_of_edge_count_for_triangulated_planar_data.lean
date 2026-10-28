-- Prove2me | solution 1 for WilliamsonShmoys.face_data_of_edge_count_for_triangulated_planar_data
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:18:19.628554+00:00
-- url     : https://prove2.me/submissions/d1288770-5c63-4372-b4ec-18b2301160fd

import Mathlib
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarFaceData

set_option autoImplicit false

namespace S216WSF

def faceEquiv (k : ℕ) (i : Fin k) : {e : Fin 3 × Fin k // e.2 = i} ≃ Fin 3 where
  toFun e := e.1.1
  invFun j := ⟨(j, i), rfl⟩
  left_inv e := by obtain ⟨⟨a, b⟩, h⟩ := e; simp only at h; subst h; rfl
  right_inv j := rfl

def edgeEquiv (k : ℕ) (i : Fin k) : {f : Fin 2 × Fin k // f.2 = i} ≃ Fin 2 where
  toFun e := e.1.1
  invFun j := ⟨(j, i), rfl⟩
  left_inv e := by obtain ⟨⟨a, b⟩, h⟩ := e; simp only at h; subst h; rfl
  right_inv j := rfl

end S216WSF

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hE : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    Nonempty (WilliamsonShmoys.TriangulatedPlanarFaceData H) := by
  classical
  set k := Fintype.card V - 2 with hk
  exact ⟨{
    Faces := Fin 2 × Fin k
    Edges := Fin 3 × Fin k
    edge_count := by simp; omega
    incident := fun f e => e.2 = f.2
    face_incidence_fintype := fun f => inferInstance
    edge_incidence_fintype := fun e => inferInstance
    euler := by simp; omega
    face_triangle := fun f => by
      rw [Fintype.card_congr (S216WSF.faceEquiv k f.2)]; simp
    edge_two_sides := fun e => by
      have : {f : Fin 2 × Fin k // e.2 = f.2} ≃ {f : Fin 2 × Fin k // f.2 = e.2} :=
        Equiv.subtypeEquivRight (fun _ => eq_comm)
      rw [Fintype.card_congr (this.trans (S216WSF.edgeEquiv k e.2))]; simp }⟩
