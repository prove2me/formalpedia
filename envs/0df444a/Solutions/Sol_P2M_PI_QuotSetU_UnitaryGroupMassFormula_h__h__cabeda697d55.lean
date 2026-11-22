-- Prove2me | solution 1 for P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__h__cabeda697d55
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:08.101946+00:00
-- url     : https://prove2.me/submissions/12979c7c-3d5c-4b7b-befa-9471bc84e47c

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) : hσ k r (hσ k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [hsig_val_eq_ite, hsig_val_eq_ite]
  split_ifs <;> omega
end PI.QuotSetU.UnitaryGroupMassFormula
