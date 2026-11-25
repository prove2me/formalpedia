-- Prove2me | solution 1 for PI.WGL.io_pol_diag_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:42.520698+00:00
-- url     : https://prove2.me/submissions/dc97bafb-8d35-41a6-85e7-48279d7dc687

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoPolDiagHw
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_pol_apply
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
theorem _root_.solution {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) (a : Fin k) :
    pol ℂ a a (hw ℂ (le_refl k) ν) = ((ν a : ℕ) : ℂ) • hw ℂ (le_refl k) ν := by
  have euler : ∀ (f : MvPolynomial (Fin k × Fin k) ℂ) (d : Fin k → ℕ),
      IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW k k) f d →
      ∑ s : Fin k, X (a, s) * pderiv (a, s) f = ((d a : ℕ) : ℂ) • f := by
    intro f d hf
    rw [f.as_sum]
    simp only [map_sum, Finset.mul_sum, MvPolynomial.X_mul_pderiv_monomial, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [← Finset.sum_smul, Nat.cast_smul_eq_nsmul]
    congr 1
    have hw' := congrFun (hf (mem_support_iff.mp hm)) a
    rw [← hw']
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Formalism.GradedWeylDivisibility.rowW, Pi.single_apply,
      Fintype.sum_prod_type]
    symm
    rw [Fintype.sum_eq_single a (fun x hx => by simp [Ne.symm hx])]
    simp
  have hH := Formalism.GradedWeylDivisibility.hwRowWeight ℂ k k (le_refl k) ν hν
  have hra : Formalism.GradedWeylDivisibility.rowNu (r := k) ν a = ν a := by
    unfold Formalism.GradedWeylDivisibility.rowNu
    rw [dif_pos a.isLt]
  rw [pol_apply, euler _ _ hH, hra]
end PI.WGL
