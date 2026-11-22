-- Prove2me | solution 1 for RSSubspaceDesign.theorem_2_14
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:40:40.055748+00:00
-- url     : https://prove2.me/submissions/33870fca-fbd3-4d16-a5af-92a10cc4dc27

import Mathlib

open Polynomial Matrix

theorem solution {E : Type*} [Field E] {t e : ℕ} (ht : 1 ≤ t) (hte : t ≤ e)
    (B : Matrix (Fin t) (Fin e) E) (D : Matrix (Fin e) (Fin t) E) :
    (B * D).det = ∑ S : {S : Finset (Fin e) // S.card = t},
      (B.submatrix id (S.1.orderEmbOfFin S.2)).det * (D.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  have hpoly : (det (1 + (X : E[X]) • ((B * D).map C)) : E[X]).coeff t =
      (det (1 + (X : E[X]) • ((D * B).map C)) : E[X]).coeff t := by
    have h := Matrix.det_one_add_mul_comm ((X : E[X]) • B.map C) (D.map C)
    rw [Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_smul, ← Matrix.map_mul] at h
    exact congrArg (fun p : E[X] => p.coeff t) h
  have hL : (det (1 + (X : E[X]) • ((B * D).map C)) : E[X]).coeff t = (B * D).det := by
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    have hpow : (Finset.univ : Finset (Fin t)).powersetCard t = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin t))
    rw [hpow, Finset.sum_singleton]
    let ee : ↥(Finset.univ : Finset (Fin t)) ≃ Fin t :=
      Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun y => ⟨⟨y, Finset.mem_univ y⟩, rfl⟩⟩
    have h := Matrix.det_submatrix_equiv_self ee (B * D)
    convert h using 1
    all_goals (congr 1)
  have hterm : ∀ S : {S : Finset (Fin e) // S.card = t},
      ((D * B).submatrix (Subtype.val : ↥(S.1) → Fin e) (Subtype.val : ↥(S.1) → Fin e)).det =
        (B.submatrix id (S.1.orderEmbOfFin S.2)).det *
          (D.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    rintro ⟨s, hs⟩
    let φ := s.orderIsoOfFin hs
    let oe := s.orderEmbOfFin hs
    let ψ : ↥s ≃ Fin t := φ.toEquiv.symm
    have hcoe : ∀ i : ↥s, (oe (ψ i) : Fin e) = ↑i := by
      intro i
      have h2 : φ (ψ i) = i := by simp [ψ]
      show ((φ (ψ i) : ↥s) : Fin e) = ((i : ↥s) : Fin e)
      rw [h2]
    have h1 : (D * B).submatrix (Subtype.val : ↥s → Fin e) (Subtype.val : ↥s → Fin e)
        = (D.submatrix (Subtype.val : ↥s → Fin e) id) *
          (B.submatrix id (Subtype.val : ↥s → Fin e)) :=
      Matrix.submatrix_mul D B _ id _ Function.bijective_id
    have hX : (D.submatrix oe id).submatrix (⇑ψ) id
        = D.submatrix (Subtype.val : ↥s → Fin e) id := by
      ext i j
      simp only [Matrix.submatrix_apply, id]
      rw [hcoe i]
    have hY : (B.submatrix id oe).submatrix id (⇑ψ)
        = B.submatrix id (Subtype.val : ↥s → Fin e) := by
      ext i j
      simp only [Matrix.submatrix_apply, id]
      rw [hcoe j]
    have h2 : ((D.submatrix oe id) * (B.submatrix id oe)).submatrix (⇑ψ) (⇑ψ)
        = (D.submatrix (Subtype.val : ↥s → Fin e) id) *
          (B.submatrix id (Subtype.val : ↥s → Fin e)) := by
      rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hX, hY]
    calc ((D * B).submatrix (Subtype.val : ↥s → Fin e) (Subtype.val : ↥s → Fin e)).det
        = ((D.submatrix (Subtype.val : ↥s → Fin e) id) *
            (B.submatrix id (Subtype.val : ↥s → Fin e))).det := by rw [h1]
      _ = (((D.submatrix oe id) * (B.submatrix id oe)).submatrix (⇑ψ) (⇑ψ)).det := by
            rw [h2]
      _ = ((D.submatrix oe id) * (B.submatrix id oe)).det :=
            Matrix.det_submatrix_equiv_self ψ _
      _ = (B.submatrix id oe).det * (D.submatrix oe id).det := by
            rw [Matrix.det_mul, mul_comm]
  have hR : (det (1 + (X : E[X]) • ((D * B).map C)) : E[X]).coeff t =
      ∑ S : {S : Finset (Fin e) // S.card = t},
        (B.submatrix id (S.1.orderEmbOfFin S.2)).det *
          (D.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    rw [Finset.sum_subtype (p := fun S : Finset (Fin e) => S.card = t)
      ((Finset.univ : Finset (Fin e)).powersetCard t)
      (fun x => by simp [Finset.mem_powersetCard])]
    exact Finset.sum_congr rfl fun S _ => hterm S
  rw [← hL, hpoly, hR]
