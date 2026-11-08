-- Prove2me | solution 1 for RegimeDRCVaR.valEC7_eq_val12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:45:41.486086+00:00
-- url     : https://prove2.me/submissions/530cad78-aab5-4968-b72e-26c2fc2fed5c

import Mathlib
import Definitions.Def_RegimeDRCVaR_valEC7
import Definitions.Def_RegimeDRCVaR_val12

open scoped ENNReal

open RegimeDRCVaR in
theorem solution {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (hm : 1 ≤ m)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (hN : ∀ k, 0 < N k) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hθ : ∀ k, 0 ≤ θ k)
    (hη0 : 0 < η) (hη1 : η < 1)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) :
    valEC7 m r w θ η A b C d = val12 m r w θ η A b C d := by
  have hc : 0 < (1 - η)⁻¹ := inv_pos.mpr (by linarith)
  apply le_antisymm
  · unfold val12
    refine le_iInf fun v => le_iInf fun x => le_iInf fun α => le_iInf fun β => le_iInf fun h => ?_
    unfold valEC7
    refine iInf_le_of_le v (iInf_le_of_le x (iInf_le_of_le α (iInf_le_of_le (fun _ => β)
      (iInf_le_of_le ⟨h.1, fun _ => h.2.1, h.2.2.1, h.2.2.2⟩ ?_))))
    apply EReal.coe_le_coe_iff.mpr
    apply le_of_eq
    have e : objEC3 w θ α (fun _ => β) =
        (∑ k, ∑ n, w k / (N k : ℝ) * α k n) + β * ∑ k, w k * θ k := by
      unfold objEC3
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    unfold obj12
    rw [e]
  · unfold valEC7
    refine le_iInf fun v => le_iInf fun x => le_iInf fun α => le_iInf fun β => le_iInf fun h => ?_
    unfold val12
    refine iInf_le_of_le v (iInf_le_of_le x (iInf_le_of_le α
      (iInf_le_of_le (normM (ENNReal.conjExponent m) x)
      (iInf_le_of_le ⟨h.1, le_rfl, h.2.2.1, h.2.2.2⟩ ?_))))
    apply EReal.coe_le_coe_iff.mpr
    unfold obj12 objEC3
    have hs : normM (ENNReal.conjExponent m) x * ∑ k, w k * θ k ≤ ∑ k, β k * w k * θ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have hwt : 0 ≤ w k * θ k := mul_nonneg (hw k) (hθ k)
      have := mul_le_mul_of_nonneg_right (h.2.1 k) hwt
      linarith [show β k * w k * θ k = β k * (w k * θ k) by ring]
    have := mul_le_mul_of_nonneg_left (add_le_add_left hs (∑ k, ∑ n, w k / (N k : ℝ) * α k n))
      hc.le
    linarith
