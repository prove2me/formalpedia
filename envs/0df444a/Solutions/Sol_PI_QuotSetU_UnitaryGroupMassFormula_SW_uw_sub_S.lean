-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_sub_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:17.370686+00:00
-- url     : https://prove2.me/submissions/7a2e7542-7986-4b50-8547-fbfc7f148ac8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply

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
theorem _root_.solution {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨h, hh, 1, ?_, (Matrix.mul_one h).symm⟩
  simp only [Nset, UH, Set.mem_setOf_eq]
  refine ⟨by simp, fun a i _ => ?_, fun i j _ _ _ => ?_⟩
  · rw [Matrix.one_apply]
  · rw [Matrix.one_apply]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
