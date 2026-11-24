-- Prove2me | solution 1 for PI.QnLevBasicsW.level_group_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:04:51.944774+00:00
-- url     : https://prove2.me/submissions/39be54a9-8a56-4ef4-9339-327c1e7f494d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_in_8b7430a5315f
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_out_3fcd34e8e182
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_apply_in_out_b74a29dc527c
import Theorems.Thm_PI_QnLevBasicsW_level_group_unitary_hermitian

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
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution : LevN := by
  intro k i r' g hg
  simp only [Nset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, h2, h3⟩ := hg
  refine ⟨level_group_unitary_hermitian k i r' g hU, ?_, ?_⟩
  · intro a p hap
    have ha := a.isLt
    by_cases hai : i ≤ a.val
    · have hbr : a.val - i < r' := by omega
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · have hpl : p.val - i < 2 * r' + k + 1 := by omega
        rw [ιLev_apply_in g p (eI k (i + r') a) ⟨p.val - i, hpl⟩ (eI k r' ⟨a.val - i, hbr⟩)
          (by simp only [Fin.val_mk]; omega) (by simp only [eI, Fin.val_mk]; omega)]
        rw [h2 ⟨a.val - i, hbr⟩ ⟨p.val - i, hpl⟩ (by simp only [Fin.val_mk]; omega)]
        simp only [Fin.ext_iff, eI, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ιLev_apply_out g p _ hp]
    · have hq : ¬ (i ≤ (eI k (i + r') a).val ∧ (eI k (i + r') a).val < 2 * r' + k + 1 + i) := by
        simp only [eI, Fin.val_mk]; omega
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · rw [ιLev_apply_in_out g p _ hp hq]
        simp only [Fin.ext_iff, eI, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ιLev_apply_out g p _ hp]
  · intro p q hq1 hq2 hp1
    have hql : q.val - i < 2 * r' + k + 1 := by omega
    by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · have hpl : p.val - i < 2 * r' + k + 1 := by omega
      rw [ιLev_apply_in g p q ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)]
      rw [h3 ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)]
      simp only [Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [ιLev_apply_out g p q hp]
end PI.QnLevBasicsW
