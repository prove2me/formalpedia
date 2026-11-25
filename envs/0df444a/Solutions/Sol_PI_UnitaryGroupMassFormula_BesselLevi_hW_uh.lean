-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.hW_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:52:43.689063+00:00
-- url     : https://prove2.me/submissions/8a7a21db-14e7-4819-af64-e118d2704284

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_tau_val
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_tau_mid
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_low_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_in
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_col_out
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_row_out
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_uh_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_mul_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_tau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
namespace PI.UnitaryGroupMassFormula.BesselLevi
theorem _root_.solution {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UH (Hpk k r)) (hX : colX k r s) : hW k r s ∈ UH (Hpk k r) := by
  have hH : ∀ i j, Hpk k r i j = sgn k r i * (if tau k r i = j then 1 else 0) := fun i j => by
    have e := hpk_mul_apply (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j
    rw [Matrix.mul_one, Matrix.one_apply] at e
    exact e
  show (hW k r s)ᴴ * Hpk k r * hW k r s = Hpk k r
  ext i j
  have := i.isLt
  have := j.isLt
  rw [uh_apply, hH]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have e := congrFun (congrFun (show sᴴ * Hpk k r * s = Hpk k r from hs) i) j
      rw [uh_apply, hH] at e
      rw [← e]
      refine Finset.sum_congr rfl fun p _ => ?_
      have := p.isLt
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [tau_mid p hp, hW_in hp hi, hW_in hp hj]
      · rcases (by omega : p.val < r ∨ r + k < p.val) with hp' | hp'
        · have htp : r + k < (tau k r p).val := by
            rw [tau_val, if_pos (Or.inl hp')]
            omega
          rw [hW_row_out p i (Or.inl hp'), if_neg (fun h => by subst h; omega), low_zero hs hX _ j htp hj.2]
          simp
        · rw [hW_row_out p i (Or.inr hp'), if_neg (fun h => by subst h; omega), low_zero hs hX p i hp' hi.2]
          simp
    · have hj' : j.val < r ∨ r + k < j.val := by omega
      rw [Finset.sum_eq_zero]
      · rw [tau_mid i hi, if_neg (fun h => by subst h; omega)]
        simp
      · intro p _
        rw [hW_col_out (tau k r p) j hj']
        by_cases hpj : tau k r p = j
        · have hp : p = tau k r j := by rw [← hpj, tau_tau]
          subst hp
          have hto : (tau k r j).val < r ∨ r + k < (tau k r j).val := by
            rw [tau_val]
            split_ifs <;> omega
          rw [hW_row_out (tau k r j) i hto, if_neg (fun h => by rw [← h] at hi; omega)]
          simp
        · rw [if_neg hpj]
          simp
  · have hi' : i.val < r ∨ r + k < i.val := by omega
    have hto : (tau k r i).val < r ∨ r + k < (tau k r i).val := by
      rw [tau_val]
      split_ifs <;> omega
    rw [Finset.sum_eq_single i]
    · rw [hW_col_out i i hi', if_pos rfl, hW_row_out (tau k r i) j hto]
      simp
    · intro p _ hp
      rw [hW_col_out p i hi', if_neg hp]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
end PI.UnitaryGroupMassFormula.BesselLevi
