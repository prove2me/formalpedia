-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_conj_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:54.392241+00:00
-- url     : https://prove2.me/submissions/15c08ec0-b9fd-4652-81bc-25ae1e32bc7d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_UW
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_uw_block
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_uw_col_out


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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {h n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : h * n * h⁻¹ ∈ Nset k r := by
  rw [mem_Nset_iff] at hn ⊢
  obtain ⟨hnU, hnc⟩ := hn
  have hU : h ∈ UH (Hpk k r) := hh.1
  have hhi := inv_mem_UW hh
  refine ⟨mul_mem_UH (mul_mem_UH hU hnU) (inv_mem_UH hU), fun i j hj hi => ?_⟩
  by_cases hjW : r ≤ j.val
  · have hir : r ≤ i.val := by
      have := min_eq_right hjW
      omega
    have hA : ∀ b, inW k r b → (h * n) i b = h i b := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · rw [hnc b b hb2 (by rw [min_eq_right hb1]; exact hb1), if_pos rfl, mul_one]
      · intro a _ hab
        by_cases har : r ≤ a.val
        · rw [hnc a b hb2 (by rw [min_eq_right hb1]; exact har), if_neg hab, mul_zero]
        · rw [uw_block hh i a (fun h' => har h'.2.1),
            if_neg (fun e => har (by rw [← e]; exact hir)), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ b) h'
    have hone : (h * h⁻¹) i j = if i = j then 1 else 0 := by
      rw [mul_inv_UH hU, Matrix.one_apply]
    rw [← hone, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : inW k r b
    · rw [hA b hb]
    · rw [uw_block hhi b j (fun h' => hb h'.1),
        if_neg (fun e => hb (by rw [e]; exact ⟨hjW, hj⟩)), mul_zero, mul_zero]
  · push Not at hjW
    have hmin : min j.val r = j.val := min_eq_left hjW.le
    have hij : j.val ≤ i.val := by omega
    have hjn : ¬ inW k r j := fun h' => absurd h'.1 (by omega)
    have hcol : (h * n * h⁻¹) i j = (h * n) i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [uw_col_out hhi j hjn j, if_pos rfl, mul_one]
      · intro b _ hb
        rw [uw_col_out hhi j hjn b, if_neg hb, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ j) h'
    rw [hcol, Matrix.mul_apply]
    by_cases hiW : inW k r i
    · have hi1 := hiW.1
      rw [if_neg (fun e => by rw [e] at hi1; omega)]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases haW : inW k r a
      · have ha1 := haW.1
        rw [hnc a j (by omega) (by rw [hmin]; omega), if_neg (fun e => by rw [e] at ha1; omega),
          mul_zero]
      · rw [uw_block hh i a (fun h' => haW h'.2), if_neg (fun e => haW (by rw [← e]; exact hiW)),
          zero_mul]
    · rw [Finset.sum_eq_single i]
      · rw [uw_block hh i i (fun h' => hiW h'.1), if_pos rfl, one_mul,
          hnc i j (by omega) (by rw [hmin]; exact hij)]
      · intro a _ hai
        rw [uw_block hh i a (fun h' => hiW h'.1), if_neg (Ne.symm hai), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ i) h'
end PI.QuotSetU.UnitaryGroupMassFormula.SW
