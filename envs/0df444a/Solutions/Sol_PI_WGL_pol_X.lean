-- Prove2me | solution 1 for PI.WGL.pol_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:15.310588+00:00
-- url     : https://prove2.me/submissions/7e32175f-d377-41b9-b4e6-32b6a84a4b1e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Theorems.Thm_PI_WGL_pol_apply
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (v : Fin r × Fin m) :
    pol R a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  classical
  rw [pol_apply]
  by_cases hv : v.1 = b
  · rw [if_pos hv, Finset.sum_eq_single v.2]
    · have : (b, v.2) = v := by rw [← hv]
      rw [this, pderiv_X_self, mul_one]
    · intro s _ hs
      rw [pderiv_X_of_ne, mul_zero]
      intro h; exact hs (by rw [h])
    · simp
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne, mul_zero]
    intro h; exact hv (by rw [h])
end PI.WGL
