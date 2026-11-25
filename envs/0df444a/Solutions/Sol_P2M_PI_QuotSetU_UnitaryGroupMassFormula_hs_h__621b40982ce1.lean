-- Prove2me | solution 1 for P2M_PI_QuotSetU_UnitaryGroupMassFormula_hs_h__621b40982ce1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:26.30905+00:00
-- url     : https://prove2.me/submissions/7377ab31-4332-483e-96ae-cc34082c34df

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
private lemma hsig_val_eq_ite (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (hσ k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold hσ
  split_ifs <;> rfl
end PI.QuotSetU.UnitaryGroupMassFormula
end
end

set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
namespace PI.QuotSetU.UnitaryGroupMassFormula
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : hs k r (hσ k r i) = hs k r i := by
  have hi := i.isLt
  simp only [hs, hsig_val_eq_ite]
  split_ifs <;> first | (exfalso; omega) | rfl
end PI.QuotSetU.UnitaryGroupMassFormula
