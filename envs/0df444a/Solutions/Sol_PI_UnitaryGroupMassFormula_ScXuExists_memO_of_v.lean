-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.memO_of_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:42.460264+00:00
-- url     : https://prove2.me/submissions/3ee3e388-87f1-47cf-84c5-148f03b55fea

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
theorem _root_.solution {x : K} (h : O.valuation x = 1) : x ∈ O :=
  (O.valuation_le_one_iff x).1 h.le
end PI.UnitaryGroupMassFormula.ScXuExists
