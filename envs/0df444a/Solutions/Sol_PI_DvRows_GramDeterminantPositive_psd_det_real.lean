-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.psd_det_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:03.97949+00:00
-- url     : https://prove2.me/submissions/b41abd27-321a-4e1a-af10-47ade5ac473f

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
theorem _root_.solution {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.det = ((A.det.re : ℝ) : ℂ) ∧ 0 ≤ A.det.re := by
  have h := hA.det_nonneg
  rw [Complex.nonneg_iff] at h
  exact ⟨Complex.ext (by simp) (by simp [← h.2]), h.1⟩
end PI.DvRows.GramDeterminantPositive
