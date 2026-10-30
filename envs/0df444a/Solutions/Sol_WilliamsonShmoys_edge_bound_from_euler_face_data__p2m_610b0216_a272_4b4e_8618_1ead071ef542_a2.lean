-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:21:05.217843+00:00
-- url     : https://prove2.me/submissions/0c486c35-5502-4a84-8e4a-8d2f22b31aa8

import Mathlib

theorem solution
    (n q e : ℕ)
    (D : Type) [Fintype D]
    (face : D → Fin q)
    (hD : Fintype.card D = 2 * e)
    (hEuler : n + q = e + 2)
    (hFaces : ∀ f : Fin q,
      3 ≤ Fintype.card {d : D // face d = f}) :
    e + 6 ≤ 3 * n := by
  let fibers : (Σ f : Fin q, {d : D // face d = f}) ≃ D :=
    { toFun := fun x => x.2.1
      invFun := fun d => ⟨face d, ⟨d, rfl⟩⟩
      left_inv := by
        intro x
        rcases x with ⟨f, ⟨d, hd⟩⟩
        cases hd
        rfl
      right_inv := by
        intro d
        rfl }
  have hsum :
      (∑ f : Fin q, Fintype.card {d : D // face d = f}) = Fintype.card D := by
    calc
      (∑ f : Fin q, Fintype.card {d : D // face d = f}) =
          Fintype.card (Σ f : Fin q, {d : D // face d = f}) := by
            symm
            exact Fintype.card_sigma
      _ = Fintype.card D := Fintype.card_congr fibers
  have hsumLower :
      3 * q ≤ ∑ f : Fin q, Fintype.card {d : D // face d = f} := by
    calc
      3 * q = ∑ _f : Fin q, (3 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ f : Fin q, Fintype.card {d : D // face d = f} :=
        Finset.sum_le_sum (fun f _ => hFaces f)
  rw [hsum, hD] at hsumLower
  omega