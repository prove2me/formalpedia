-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_polytope_integral_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:35:02.725958+00:00
-- url     : https://prove2.me/submissions/593ed21d-81fe-4080-a57e-03e2c3e10d54

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QMCMatch_Main
import Mathlib
open scoped BigOperators

theorem solution {n : ℕ} (w : QuantumMaxCutEnergy.Weights n)
    (x : QuantumMaxCutEnergy.Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤ ((S.card : ℝ) - 1) / 2) :
    ∃ M : Finset (QuantumMaxCutEnergy.Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (∑ e, (w e : ℝ) * x e) ≤ ∑ e ∈ M, (w e : ℝ) :=
  QMCMatch.edmonds_rat w x hx hload hodd
