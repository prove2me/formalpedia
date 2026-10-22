-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.reducible_residues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:08:52.954629+00:00
-- url     : https://prove2.me/submissions/991ccbdb-3846-4c7f-8e5a-c0f64afb2bb1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Remark 7.5, PDF p.8: complete classification in Z[omega]/(2), using the
source's pqrs convention rather than reduction modulo sqrt(2). -/
theorem solution (r : Residue) :
    Reducible r ↔ r = bits 0 ∨ r = bits 5 ∨ r = bits 10 ∨ r = bits 15 := by
  revert r
  unfold Reducible residueMultiply bits
  decide


end
