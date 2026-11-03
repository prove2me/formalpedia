-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_rank3_gaussian_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T19:20:02.925309+00:00
-- url     : https://prove2.me/submissions/ffe00ee5-af9d-4528-ab7d-3784ab65e44b

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Theorems.Thm_QuantumMaxCutEnergy_rank3_gaussian_expectation_identity
import Theorems.Thm_QuantumMaxCutEnergy_rank3_odd_series_ratio_0954
open scoped BigOperators

theorem solution (n : ℕ) (w : QuantumMaxCutEnergy.Weights n)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    ∃ r : Fin n → Fin 3 → ℝ,
      (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
      (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
          (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) ≤
        0.046 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ)) +
          0.954 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * X e.val.1 e.val.2) := by
  -- The Gaussian expectation identity now isolates the analytic core;
  -- its second conjunct is exactly the desired rounding inequality.
  obtain ⟨F, ⟨c, hc0, hc1, hc2, hc3, hc4, hF⟩, hr⟩ :=
    QuantumMaxCutEnergy.rank3_gaussian_expectation_identity n X hX hdiag
  exact hr w
