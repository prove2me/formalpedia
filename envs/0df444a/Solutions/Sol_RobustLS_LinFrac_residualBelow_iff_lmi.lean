-- Prove2me | solution 1 for RobustLS.LinFrac.residualBelow_iff_lmi
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:58:31.415989+00:00
-- url     : https://prove2.me/submissions/69b63104-a1b2-4c1a-80e7-b7355d2bdd86

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

theorem aux_rlfi_ident {n m N : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) (Δ : Matrix (Fin N) (Fin N) ℝ) :
    residualLMI A b L RA Rb D x lam Δ =
      Matrix.fromBlocks (lam • (1 : Matrix (Fin n) (Fin n) ℝ))
        (replicateCol Unit (pertA A L RA D Δ *ᵥ x - pertB b L Rb D Δ))
        (replicateRow Unit (pertA A L RA D Δ *ᵥ x - pertB b L Rb D Δ))
        (lam • (1 : Matrix Unit Unit ℝ)) := by
  unfold residualLMI
  simp only [fromRows_mul, mul_fromCols, Matrix.mul_zero, Matrix.zero_mul, ← replicateCol_mulVec,
    ← replicateRow_vecMul, vecMul_transpose]
  have hv : pertA A L RA D Δ *ᵥ x - pertB b L Rb D Δ
      = A *ᵥ x - b + L *ᵥ (Δ *ᵥ ((1 - D * Δ)⁻¹ *ᵥ (RA *ᵥ x - Rb))) := by
    simp only [pertA, pertB, add_mulVec, mulVec_mulVec, mulVec_sub, Matrix.mul_assoc]
    abel
  rw [hv, mulVec_mulVec, mulVec_mulVec]
  ext (i | i) (j | j) <;> simp [replicateCol, replicateRow, Matrix.mul_assoc]

theorem aux_rlfi_quad {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) (z : Fin n ⊕ Unit → ℝ) :
    star z ⬝ᵥ (Matrix.fromBlocks (lam • (1 : Matrix (Fin n) (Fin n) ℝ)) (replicateCol Unit v)
      (replicateRow Unit v) (lam • (1 : Matrix Unit Unit ℝ)) *ᵥ z) =
      lam * ∑ i, z (Sum.inl i) ^ 2 + 2 * z (Sum.inr ()) * ∑ i, v i * z (Sum.inl i)
        + lam * z (Sum.inr ()) ^ 2 := by
  simp only [star_trivial, dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec]
  simp [replicateCol, replicateRow, mulVec, one_apply, dotProduct]
  have e1 : ∑ x, z (Sum.inl x) * (lam * z (Sum.inl x) + v x * z (Sum.inr ()))
      = lam * ∑ x, z (Sum.inl x) ^ 2 + z (Sum.inr ()) * ∑ x, v x * z (Sum.inl x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  ring

theorem aux_rlfi_pd {n : ℕ} (v : Fin n → ℝ) (lam : ℝ) :
    (Matrix.fromBlocks (lam • (1 : Matrix (Fin n) (Fin n) ℝ)) (replicateCol Unit v)
      (replicateRow Unit v) (lam • (1 : Matrix Unit Unit ℝ))).PosDef ↔ eucNorm v < lam := by
  have hs0 : 0 ≤ eucNorm v := Real.sqrt_nonneg _
  have hsq : eucNorm v ^ 2 = ∑ i, v i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  constructor
  · intro h
    have hlam : 0 < lam := by
      have := h.diag_pos (i := Sum.inr ())
      simpa [fromBlocks] using this
    by_contra hle
    rw [not_lt] at hle
    have hspos : 0 < eucNorm v := lt_of_lt_of_le hlam hle
    let z : Fin n ⊕ Unit → ℝ := Sum.elim (-v) (fun _ => eucNorm v)
    have hz : z ≠ 0 := by
      intro h0
      have := congrFun h0 (Sum.inr ())
      simp [z] at this
      linarith
    have hq := h.dotProduct_mulVec_pos hz
    rw [aux_rlfi_quad] at hq
    simp only [z, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply] at hq
    have e2 : ∑ i, (-v i) ^ 2 = eucNorm v ^ 2 := by simp [hsq]
    have e3 : ∑ i, v i * -v i = -(eucNorm v ^ 2) := by
      rw [hsq, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e2, e3] at hq
    nlinarith
  · intro h
    have hlam : 0 < lam := lt_of_le_of_lt hs0 h
    refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [fromBlocks, one_apply, eq_comm, replicateCol, replicateRow]
    · intro z hz
      rw [aux_rlfi_quad]
      set Y := ∑ i, z (Sum.inl i) ^ 2 with hYdef
      set t := z (Sum.inr ()) with htdef
      set P := ∑ i, v i * z (Sum.inl i) with hPdef
      have hY : 0 ≤ Y := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hCS : P ^ 2 ≤ (∑ i, v i ^ 2) * Y := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      have hpos : 0 < Y + t ^ 2 := by
        by_contra hc
        rw [not_lt] at hc
        have hY0 : Y = 0 := by nlinarith [sq_nonneg t]
        have ht0 : t = 0 := by nlinarith [sq_nonneg t]
        apply hz
        ext k
        rcases k with i | u
        · have := (Finset.sum_eq_zero_iff_of_nonneg
            (fun i _ => sq_nonneg (z (Sum.inl i)))).1 hY0 i (Finset.mem_univ _)
          simpa using this
        · cases u
          simpa using ht0
      have hl2 : eucNorm v ^ 2 < lam ^ 2 := by nlinarith
      have h4 : (2 * t * P) ^ 2 < (lam * (Y + t ^ 2)) ^ 2 := by
        calc (2 * t * P) ^ 2 = 4 * t ^ 2 * P ^ 2 := by ring
          _ ≤ 4 * t ^ 2 * ((∑ i, v i ^ 2) * Y) :=
              mul_le_mul_of_nonneg_left hCS (by positivity)
          _ = eucNorm v ^ 2 * (4 * Y * t ^ 2) := by rw [hsq]; ring
          _ ≤ eucNorm v ^ 2 * (Y + t ^ 2) ^ 2 :=
              mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (Y - t ^ 2)]) (by positivity)
          _ < lam ^ 2 * (Y + t ^ 2) ^ 2 :=
              mul_lt_mul_of_pos_right hl2 (by positivity)
          _ = (lam * (Y + t ^ 2)) ^ 2 := by ring
      have h5 := abs_lt_of_sq_lt_sq h4 (by positivity)
      have h6 := neg_abs_le (2 * t * P)
      nlinarith [abs_lt.mp h5]

end RobustLS.LinFrac

open RobustLS.LinFrac

theorem solution {n m N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) (L : Matrix (Fin n) (Fin N) ℝ)
    (RA : Matrix (Fin N) (Fin m) ℝ) (Rb : Fin N → ℝ) (D : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    ResidualBelow 𝒟 A b L RA Rb D x lam ↔
      ∀ Δ ∈ 𝒟, specNorm Δ ≤ 1 →
        (1 - D * Δ).det ≠ 0 ∧ (residualLMI A b L RA Rb D x lam Δ).PosDef := by
  unfold ResidualBelow
  refine forall_congr' fun Δ => forall_congr' fun _ => forall_congr' fun _ =>
    and_congr_right fun _ => ?_
  rw [aux_rlfi_ident, aux_rlfi_pd]
