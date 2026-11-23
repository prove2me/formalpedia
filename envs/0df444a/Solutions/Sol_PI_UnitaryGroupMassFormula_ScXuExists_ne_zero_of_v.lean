-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.ne_zero_of_v
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:27.098509+00:00
-- url     : https://prove2.me/submissions/f01580df-ac41-4bff-8342-7edc09ccb3b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution {x : K} (h : O.valuation x = 1) : x ≠ 0 := by
  rintro rfl
  simp at h
end PI.UnitaryGroupMassFormula.ScXuExists
