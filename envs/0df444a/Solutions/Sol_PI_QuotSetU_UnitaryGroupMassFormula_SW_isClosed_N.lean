-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.isClosed_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:16:07.105397+00:00
-- url     : https://prove2.me/submissions/e7b83533-43d9-4888-a42c-4b5c8c78d840

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_isClosed_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff


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
theorem _root_.solution : IsClosed (Nset k r) := by
  have e : Nset k r = UH (Hpk k r) ∩ ⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1),
      {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
        j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} := by
    ext g
    rw [mem_Nset_iff]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_UH.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  by_cases hp : j.val ≤ r + k ∧ min j.val r ≤ i.val
  · have : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
        j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        {g | g i j = if i = j then 1 else 0} := by
      ext g; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hp.1 hp.2, fun h _ _ => h⟩
    rw [this]
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · have : {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
        j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} = Set.univ := by
      ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ hp
    rw [this]; exact isClosed_univ
end PI.QuotSetU.UnitaryGroupMassFormula.SW
