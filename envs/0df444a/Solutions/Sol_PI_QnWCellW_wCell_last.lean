-- Prove2me | solution 1 for PI.QnWCellW.wCell_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:53.529176+00:00
-- url     : https://prove2.me/submissions/495a8916-df9d-450e-b0fb-ac6701903522

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
import Theorems.Thm_PI_QnWCellW_prod_eq_Wm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.QnWCellW.cN_val

set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnWCellW
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) : wCell k r (Fin.last r) c = Wm k r (Finset.range r) c := by
  unfold wCell
  rw [List.filter_eq_self.mpr (fun a _ => by simp [a.isLt]), prod_eq_Wm k r c _ (List.nodup_finRange r)]
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and, Finset.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isLt
  · intro hj
    exact ⟨⟨j, hj⟩, rfl⟩
end PI.QnWCellW
