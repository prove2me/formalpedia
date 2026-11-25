-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.inv_memO_of_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:24.176427+00:00
-- url     : https://prove2.me/submissions/8b38a022-6a03-4aca-ae2c-a3e475bad5ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_memO_of_v

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
theorem _root_.solution {x : K} (h : O.valuation x = 1) : x⁻¹ ∈ O :=
  memO_of_v O (by rw [map_inv₀, h, inv_one])
end PI.UnitaryGroupMassFormula.ScXuExists
