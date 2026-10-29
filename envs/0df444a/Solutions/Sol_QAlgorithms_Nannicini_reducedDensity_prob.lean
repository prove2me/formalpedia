-- Prove2me | solution 1 for QAlgorithms.Nannicini.reducedDensity_prob
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-10-29T01:31:26.617689+00:00
-- url     : https://prove2.me/submissions/74e12c1d-8892-4d17-9d41-92ae71b55066

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

open QAlgorithms
open scoped ComplexOrder

theorem solution {ma mb : ℕ}
    (ρ : Matrix (Qubits ma × Qubits mb) (Qubits ma × Qubits mb) ℂ) (hρ : IsDensityMatrix ρ)
    (j : Qubits ma) :
    densityProb (traceRight ρ) j = ∑ k : Qubits mb, densityProb ρ (j, k) := by
  simp [densityProb, traceRight]

#print axioms solution
