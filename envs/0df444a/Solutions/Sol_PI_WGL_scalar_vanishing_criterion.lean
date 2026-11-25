-- Prove2me | solution 1 for PI.WGL.scalar_vanishing_criterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:24.11601+00:00
-- url     : https://prove2.me/submissions/56139d3d-940b-4724-be17-209b6bae33fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_NumMore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionNum
import Theorems.Thm_PI_GTNum_sg_mem_R


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution : ZScalarVanish := by
  intro n N h lam sg mu hsg hmu hne hw
  have hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i := by
    unfold wsum at hw
    exact hw
  have hD : D0 h lam mu = D0 h lam sg := by
    unfold D0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hmem : mu.w i ∈ Rset h lam sg i := by
    have hm := PI.GTNum.sg_mem_R h lam mu hmu i
    unfold Rset at hm ⊢
    rw [hD] at hm
    exact hm
  unfold zScalar
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring
end PI.WGL
