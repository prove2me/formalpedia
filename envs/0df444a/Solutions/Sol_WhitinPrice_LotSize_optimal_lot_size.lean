-- Prove2me | solution 1 for WhitinPrice.LotSize.optimal_lot_size
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:29:18.869274+00:00
-- url     : https://prove2.me/submissions/d46f8292-b0e4-4933-a4fb-be26c7fcebe4

import Definitions.Def_WhitinPrice_LotSize_Model

set_option autoImplicit false
open WhitinPrice.LotSize

theorem solution (S I C k D : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C) (hD : 0 < D) :
    0 < Real.sqrt (2 * D * S / (I * C)) ∧
      ∀ Q : ℝ, 0 < Q →
        tvc S I C k D (Real.sqrt (2 * D * S / (I * C))) ≤ tvc S I C k D Q ∧
          (tvc S I C k D (Real.sqrt (2 * D * S / (I * C))) = tvc S I C k D Q →
            Q = Real.sqrt (2 * D * S / (I * C))) := by
  let q := Real.sqrt (2 * D * S / (I * C))
  have hIC : 0 < I * C := mul_pos hI hC
  have hrad : 0 < 2 * D * S / (I * C) := by positivity
  have hq : 0 < q := Real.sqrt_pos.2 hrad
  have hsq : q ^ 2 * (I * C) = 2 * D * S := by
    have hs := Real.sq_sqrt (le_of_lt hrad)
    dsimp [q]
    rw [hs]
    exact div_mul_cancel₀ _ (ne_of_gt hIC)
  have hopt : tvc S I C k D q = q * (I * C) + k * D := by
    unfold tvc InventoryControl.eoqCost
    field_simp [ne_of_gt hq]
    nlinarith [hsq]
  refine ⟨hq, ?_⟩
  intro Q hQ
  have hgap : tvc S I C k D Q - tvc S I C k D q =
      (I * C) * (Q - q) ^ 2 / (2 * Q) := by
    rw [hopt]
    unfold tvc InventoryControl.eoqCost
    field_simp [ne_of_gt hQ]
    nlinarith [hsq]
  have hnonneg : 0 ≤ (I * C) * (Q - q) ^ 2 / (2 * Q) := by positivity
  constructor
  · linarith
  · intro heq
    have hz : (I * C) * (Q - q) ^ 2 = 0 := by
      have : (I * C) * (Q - q) ^ 2 / (2 * Q) = 0 := by linarith
      exact (div_eq_zero_iff).1 this |>.resolve_right (by positivity)
    have : (Q - q) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hIC)
    nlinarith
