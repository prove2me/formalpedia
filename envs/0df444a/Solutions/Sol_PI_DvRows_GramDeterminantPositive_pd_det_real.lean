-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.pd_det_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:57.018767+00:00
-- url     : https://prove2.me/submissions/8dedf246-c7c6-4d58-9a58-30b5b970ced6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution {A : Matrix n n ℂ} (hA : A.PosDef) :
    A.det = ((A.det.re : ℝ) : ℂ) ∧ 0 < A.det.re := by
  have h := hA.det_pos
  rw [Complex.lt_def] at h
  refine ⟨Complex.ext (by simp) (by simp [← h.2]), by simpa using h.1⟩
end PI.DvRows.GramDeterminantPositive
