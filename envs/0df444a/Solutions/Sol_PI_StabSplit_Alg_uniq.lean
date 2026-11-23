-- Prove2me | solution 1 for PI.StabSplit.Alg.uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:38.393992+00:00
-- url     : https://prove2.me/submissions/3a5ed81c-fb18-4154-a796-f9adc74e0777

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
theorem _root_.solution (h P ρ κ : R) (hρκ : ρ * κ = h) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hκU : P * κ * (1 - P) = 0) :
    ρ = h * P + (1 - P) ∧ κ = h * (1 - P) + P := by
  have a : ρ * κ - h = 0 := sub_eq_zero.mpr hρκ
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  constructor
  · have e : ρ - (h * P + (1 - P)) = (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) := by
      noncomm_ring
    have z : (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) = 0 := by
      simp only [a, b, c, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)
  · have e : κ - (h * (1 - P) + P) = (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) := by
      noncomm_ring
    have z : (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) = 0 := by
      simp only [a, b, c, hκU, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)
end PI.StabSplit.Alg
