-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_indexed_face_data__p2m_ebf5989a_e833_400a_bb03_e76531d49638_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:13:59.772513+00:00
-- url     : https://prove2.me/submissions/4b7c4ab0-44a1-4171-811c-287419f340a2

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (F : Type) [Fintype F]
    (M : WilliamsonShmoys.TriangularMap H F) :
    ∃ (m : Nat) (length : Fin m → Nat)
      (corner : ∀ f, Fin (length f) → V)
      (dart : (Σ f : Fin m, Fin (length f)) ≃ H.Dart),
      (∀ f, length f = 3) ∧
      (∀ f i, (dart ⟨f, i⟩).fst = corner f i) ∧
      (∀ f i, (dart ⟨f, i⟩).snd =
        corner f ⟨(i.val + 1) % length f, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) ∧
      H.Connected ∧
      (∀ d e : H.Dart, d.fst = e.fst →
        ∃ k : Nat,
          (fun a : H.Dart =>
            dart ⟨(dart.symm a.symm).1,
              ⟨(((dart.symm a.symm).2).val + 1) % length ((dart.symm a.symm).1),
                Nat.mod_lt _ (Nat.zero_lt_of_lt ((dart.symm a.symm).2).isLt)⟩⟩)^[k] d = e) := by
  classical
  let faceEquiv : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let length : Fin (Fintype.card F) → Nat := fun _ => 3
  let corner : ∀ f, Fin (length f) → V := fun f i => M.corner (faceEquiv f) i
  let dart : (Σ f : Fin (Fintype.card F), Fin (length f)) ≃ H.Dart :=
    { toFun := fun a => M.dart (faceEquiv a.1, a.2)
      invFun := fun d => ⟨faceEquiv.symm (M.dart.symm d).1, (M.dart.symm d).2⟩
      left_inv := by
        rintro ⟨f, i⟩
        simp [faceEquiv, length]
      right_inv := by
        intro d
        simp [faceEquiv, length] }
  have modularSucc (i : Fin 3) :
      (⟨(i.val + 1) % 3, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin 3) = i + 1 := by
    fin_cases i <;> decide
  let rot : H.Dart → H.Dart := fun a =>
    dart ⟨(dart.symm a.symm).1,
      ⟨(((dart.symm a.symm).2).val + 1) % length ((dart.symm a.symm).1),
        Nat.mod_lt _ (Nat.zero_lt_of_lt ((dart.symm a.symm).2).isLt)⟩⟩
  let rotSource : H.Dart → H.Dart := fun a =>
    M.dart ((M.dart.symm a.symm).1, (M.dart.symm a.symm).2 + 1)
  have hrot : rot = rotSource := by
    funext a
    simp [rot, rotSource, dart, length, modularSucc]
  refine ⟨Fintype.card F, length, corner, dart, ?_, ?_, ?_, ?_, ?_, M.connected, ?_⟩
  · intro f
    rfl
  · intro f i
    simpa [dart, corner] using M.dart_tail (faceEquiv f) i
  · intro f i
    simpa [dart, corner, length, modularSucc] using M.dart_head (faceEquiv f) i
  · intro f
    exact M.corners_distinct (faceEquiv f)
  · intro v
    rcases M.vertex_covered v with ⟨f, i, hi⟩
    exact ⟨faceEquiv.symm f, i, by simpa [corner, faceEquiv] using hi⟩
  · intro d e hde
    change ∃ k : Nat, (rot^[k]) d = e
    rcases M.rotation_transitive d e hde with ⟨k, hk⟩
    exact ⟨k, by rw [hrot]; exact hk⟩
