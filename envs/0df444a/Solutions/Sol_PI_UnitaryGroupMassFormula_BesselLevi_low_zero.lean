-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.low_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:43:14.150659+00:00
-- url     : https://prove2.me/submissions/6143374f-a2af-4c43-a389-abfa7e94ec87

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_colX_of_left_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_tau_val
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_sgn_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_inv_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_inv_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
namespace PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
private theorem inv_mul_eq_one_of_mem_UH_Hpk {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) : s⁻¹ * s = 1 := by
  rw [inv_eq hs]
  have e : Hpk k r * sᴴ * Hpk k r * s = Hpk k r * (sᴴ * Hpk k r * s) := by simp only [Matrix.mul_assoc]
  rw [e, show sᴴ * Hpk k r * s = Hpk k r from hs, hpk_sq]
end PI.UnitaryGroupMassFormula.BesselLevi
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
namespace PI.UnitaryGroupMassFormula.BesselLevi
theorem _root_.solution {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (hX : colX k r s) (i j : Fin (2 * r + k + 1))
    (hi : r + k < i.val) (hj : j.val ≤ r + k) : s i j = 0 := by
  have hinv := inv_mul_eq_one_of_mem_UH_Hpk hs
  have hc := colX_of_left_inv hX hinv
  have := i.isLt
  have := j.isLt
  have hti : (tau k r i).val < r := by
    rw [tau_val, if_pos (Or.inr hi)]
    omega
  have hle : (tau k r i).val ≤ (tau k r j).val := by
    rw [tau_val, tau_val]
    split_ifs <;> omega
  have e := hc (tau k r j) (tau k r i) hti hle
  have hne : tau k r j ≠ tau k r i := by
    intro h
    have h2 := congrArg (tau k r) h
    rw [tau_tau, tau_tau] at h2
    subst h2
    omega
  rw [inv_apply hs, tau_tau, tau_tau, if_neg hne] at e
  rcases mul_eq_zero.mp e with h | h
  · exact absurd h (sgn_ne _)
  · rcases mul_eq_zero.mp h with h' | h'
    · exact star_eq_zero.mp h'
    · exact absurd h' (sgn_ne _)
end PI.UnitaryGroupMassFormula.BesselLevi
