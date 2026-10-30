-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P03.optimal_ancilla_charge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:07:04.126504+00:00
-- url     : https://prove2.me/submissions/68bfcf86-7e6c-452a-bbe3-7f3dba4fad7d

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

open QAlgorithms.Papers.Independent.Extend50.P03

theorem s110_cc_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (4 * Real.sqrt y)⁻¹ ≤ (4 * Real.sqrt x)⁻¹ := by
  have h1 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  apply inv_anti₀ (by positivity)
  have := Real.sqrt_le_sqrt hxy
  linarith

theorem solution :
    (∀ a : ℝ, 0 < a → a < 1 →
      chargeCoefficient (1/2) ≤ chargeCoefficient a ∧
      (chargeCoefficient a = chargeCoefficient (1/2) ↔ a = 1/2)) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1/2 → chargeCoefficient b ≤ chargeCoefficient a) ∧
    (∀ a b : ℝ, 1/2 ≤ a → a ≤ b → b < 1 → chargeCoefficient a ≤ chargeCoefficient b) := by
  refine ⟨fun a ha0 ha1 => ⟨?_, ?_⟩, fun a b ha hab hb => ?_, fun a b ha hab hb => ?_⟩
  · unfold chargeCoefficient
    apply s110_cc_anti (by nlinarith)
    nlinarith [sq_nonneg (a - 1/2)]
  · constructor
    · intro h
      unfold chargeCoefficient at h
      have hp : 0 < a * (1 - a) := by nlinarith
      have h2 : Real.sqrt (a * (1 - a)) = Real.sqrt (1/2 * (1 - 1/2)) := by
        have h' := congrArg (fun t => t⁻¹) h
        simp only [inv_inv] at h'
        linarith
      have h3 : a * (1 - a) = 1/2 * (1 - 1/2) :=
        (Real.sqrt_inj hp.le (by norm_num)).1 h2
      nlinarith [sq_nonneg (a - 1/2)]
    · rintro rfl; rfl
  · unfold chargeCoefficient
    apply s110_cc_anti (by nlinarith)
    nlinarith
  · unfold chargeCoefficient
    apply s110_cc_anti (by nlinarith)
    nlinarith
