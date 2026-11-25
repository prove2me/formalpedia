-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.n_ut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:17.36803+00:00
-- url     : https://prove2.me/submissions/28c036a5-a5ed-4e43-8bd9-f96c60dd9c63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nc_inv
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mul_mul_Hpk_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_eq_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r)
    (i j : Fin (2 * r + k + 1)) (hij : j.val ≤ i.val) : n i j = if i = j then 1 else 0 := by
  obtain ⟨hU, hN⟩ := (mem_Nset_iff n).1 hn
  by_cases hj : j.val ≤ r + k
  · exact hN i j hj (le_trans (min_le_left _ _) hij)
  · push_neg at hj
    have hinv : NC k r n⁻¹ := nc_inv hU hN
    have hvj : (piI k r j).val = 2 * r + k - j.val := by
      rw [piI_val, if_neg (by omega)]
    have hvi : (piI k r i).val = 2 * r + k - i.val := by
      rw [piI_val, if_neg (by omega)]
    have h1 := hinv (piI k r j) (piI k r i) (by omega)
      (by rw [hvi, hvj, min_eq_left (by omega)]; omega)
    rw [inv_eq_UH hU, Hpk_mul_mul_Hpk_apply, piI_piI, piI_piI, conjTranspose_apply] at h1
    have he1 : epsI k r (piI k r j) = 1 := by
      simp only [epsI]; rw [if_neg (by omega)]
    have he2 : epsI k r (piI k r i) = 1 := by
      simp only [epsI]; rw [if_neg (by omega)]
    rw [he1, he2, one_mul, mul_one] at h1
    have h2 := congrArg star h1
    rw [star_star] at h2
    rw [h2]
    by_cases hij' : i = j
    · subst hij'
      simp
    · have hne : piI k r j ≠ piI k r i := by
        intro h
        have h' := congrArg (piI k r) h
        rw [piI_piI, piI_piI] at h'
        exact hij' h'.symm
      rw [if_neg hne, if_neg hij', star_zero]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
