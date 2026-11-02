-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_finite_product_estimator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T15:03:40.547534+00:00
-- url     : https://prove2.me/submissions/c8e3735a-7c9c-475b-8dd6-995f34d4f790
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QuantumMaxCutEnergy_agm_deterministic_product_value_program

noncomputable section
open scoped BigOperators
open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open QMCNumericRuntime

theorem solution :
    ∃ P : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime P ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (∀ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
          (P.run G (List.ofFn r) : ℝ) ≤ QuantumMaxCutEnergy.optimum G) ∧
        (0.953 : ℝ) * (QuantumMaxCutEnergy.optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
          (∑ r : Fin (QuantumMaxCutEnergy.randomBits P G) → Bool,
            (P.run G (List.ofFn r) : ℝ)) /
            (Fintype.card (Fin (QuantumMaxCutEnergy.randomBits P G) → Bool) : ℝ) := by
  obtain ⟨p, ⟨PA⟩, hp⟩ := agm_deterministic_product_value_program
  let P : Algorithm := { randomFactor := 0, randomDegree := 0, run := fun G _ => p G }
  let nonnegativeProgram : PolyProgram encodeRequest (fun q : ℚ≥0 => Ratio.encode (q : ℚ))
      (fun request : Input × List Bool => P.run request.1 request.2) :=
    PA.recode id (fun _ => rfl) (fun _ => rfl)
  have hPtime : PolynomialTime P := ⟨(nonnegativeProgram.comp nnratOutput).stock⟩
  refine ⟨P, hPtime, ?_⟩
  intro G
  refine ⟨fun _ => (hp G).1, ?_⟩
  have hc : (Fintype.card (Fin (randomBits P G) → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (0.953 : ℝ) * (optimum G + (∑ e, (G.weights e : ℝ))) / 3 ≤
    (∑ _r : Fin (randomBits P G) → Bool, (p G : ℝ)) /
      (Fintype.card (Fin (randomBits P G) → Bool) : ℝ)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hc]
  exact (hp G).2

#print axioms solution
