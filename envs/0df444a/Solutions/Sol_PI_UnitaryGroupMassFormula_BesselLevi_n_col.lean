-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.n_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:52:47.469661+00:00
-- url     : https://prove2.me/submissions/84bade18-3839-4979-91b6-cca07d913d35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_colX_of_left_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_inv_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_low_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_in
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_col_out
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_row_out
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq

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
    (hs : s ∈ UH (Hpk k r)) (hX : colX k r s) : col k r (s⁻¹ * hW k r s) := by
  intro i j hj hij
  have hinv := inv_mul_eq_one_of_mem_UH_Hpk hs
  have hc := colX_of_left_inv hX hinv
  have := i.isLt
  have := j.isLt
  rw [Matrix.mul_apply]
  by_cases hjr : j.val < r
  · rw [Finset.sum_eq_single j]
    · rw [hW_col_out j j (Or.inl hjr), if_pos rfl, mul_one]
      exact hc i j hjr (by omega)
    · intro l _ hl
      rw [hW_col_out l j (Or.inl hjr), if_neg hl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hjm : r ≤ j.val ∧ j.val ≤ r + k := ⟨by omega, hj⟩
    have hir : r ≤ i.val := by omega
    have e := congrFun (congrFun hinv i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    rw [← e]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := l.isLt
    by_cases hlm : r ≤ l.val ∧ l.val ≤ r + k
    · rw [hW_in hlm hjm]
    · rcases (by omega : l.val < r ∨ r + k < l.val) with hl | hl
      · rw [hc i l hl (by omega), if_neg (fun h => by subst h; omega), zero_mul, zero_mul]
      · rw [hW_row_out l j (Or.inr hl), if_neg (fun h => by subst h; omega), low_zero hs hX l j hl hj,
          mul_zero]
end PI.UnitaryGroupMassFormula.BesselLevi
