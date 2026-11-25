-- Prove2me | solution 1 for PI.WMI.MMap.weight_colW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:18.148913+00:00
-- url     : https://prove2.me/submissions/947264cf-569f-44de-8c58-cf92d83bf85e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
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
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
open PI.WMI.MMap
namespace PI.WMI.MMap
theorem _root_.solution {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (s : Fin N) :
    Finsupp.weight (colW N N) m s = ∑ v : Fin N × Fin N, if v.2 = s then m v else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.2 = s
  · subst h; simp [colW]
  · simp [colW, h, Ne.symm h]
end PI.WMI.MMap
