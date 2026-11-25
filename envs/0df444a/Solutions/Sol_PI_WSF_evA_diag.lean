-- Prove2me | solution 1 for PI.WSF.evA_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:20.272883+00:00
-- url     : https://prove2.me/submissions/9c72151b-5a43-4aae-bcd9-e4be2e908c0f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory
namespace PI.WSF
theorem _root_.solution {N : ℕ} (d : Fin N × Fin N →₀ ℕ)
    (h : (∏ v ∈ d.support, ((1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) ^ d v) ≠ 0) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N) d := by
  have hdiag : ∀ v ∈ d.support, v.1 = v.2 := by
    intro v hv
    by_contra hne
    apply h
    apply Finset.prod_eq_zero hv
    rw [Matrix.one_apply_ne hne]
    exact zero_pow (Finsupp.mem_support_iff.mp hv)
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun v hv => ?_
  simp [Formalism.GradedWeylDivisibility.rowW, Formalism.GradedWeylDivisibility.colW, hdiag v hv]
end PI.WSF
