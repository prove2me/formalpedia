-- Prove2me | solution 1 for PI.StabSplit.Alg.comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:02.957005+00:00
-- url     : https://prove2.me/submissions/8f20745b-7eb8-4dfb-a9e5-db6f7ee3001a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.StabSplit PI.StabSplit.Alg
variable {R : Type*} [Ring R]
namespace PI.StabSplit.Alg
theorem _root_.solution (P ρ κ : R) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hρM : (1 - P) * ρ * P = 0) (hκU : P * κ * (1 - P) = 0) : ρ * κ = κ * ρ := by
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  have e : ρ * κ - κ * ρ = ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) := by
    noncomm_ring
  have z : ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) = 0 := by
    simp only [b, c, hρM, hκU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)
end PI.StabSplit.Alg
