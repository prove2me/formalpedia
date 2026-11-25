-- Prove2me | solution 1 for PI.QnLevBasicsW.level_group_unitary_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:55.610968+00:00
-- url     : https://prove2.me/submissions/f1d683de-400c-41fe-ae33-c810f89b002e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_PI_QnLevBasicsW_col_fix
import Theorems.Thm_PI_QnLevBasicsW_level_group_unitary_hermitian
import Theorems.Thm_PI_QnLevBasicsW_mulVec_lift


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
theorem _root_.solution : LevUW := by
  intro k i r' z g hg
  simp only [UWset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hfix, hz⟩ := hg
  refine ⟨level_group_unitary_hermitian k i r' g hU, fun a => ⟨?_, ?_⟩, ?_⟩
  · apply col_fix
    intro b hb
    have ha := a.isLt
    have hbr : b.val < r' := by simp only [eI, Fin.val_mk] at hb; omega
    have e : b = eI k r' ⟨b.val, hbr⟩ := Fin.ext rfl
    rw [e]
    exact (hfix ⟨b.val, hbr⟩).1
  · apply col_fix
    intro b hb
    have ha := a.isLt
    have hb' := b.isLt
    have hai : i ≤ a.val := by simp only [esI, Fin.val_mk] at hb; omega
    have hcr : a.val - i < r' := by omega
    have e : b = esI k r' ⟨a.val - i, hcr⟩ := by
      apply Fin.ext
      simp only [esI, Fin.val_mk] at hb ⊢
      omega
    rw [e]
    exact (hfix ⟨a.val - i, hcr⟩).2
  · rw [mulVec_lift, hz]
end PI.QnLevBasicsW
