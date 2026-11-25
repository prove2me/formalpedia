-- Prove2me | solution 1 for PI.WMI.model_map_equivariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:17.372683+00:00
-- url     : https://prove2.me/submissions/d7243e5b-bcc8-45e0-b7b6-53ef861f9a2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Theorems.Thm_PI_WMI_MMap_weight_colW
import Theorems.Thm_PI_WMI_MMap_Fl_apply
import Theorems.Thm_PI_WMI_MMap_Fq_intertwine
import Theorems.Thm_PI_WMI_MMap_Fq_colAdd
import Theorems.Thm_PI_WMI_MMap_Fq_deg
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylPoint
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
open MMap
namespace PI.WMI
theorem _root_.solution : ModelMap := by
  intro N V _ _ _ P v0 μ K hP hv0 htor hlow
  have hF0 : Fq hP v0 v0 ≠ 0 := by
    intro h
    have h1 := evM_Fq hP v0 v0 1
    rw [h, Matrix.transpose_one, hP.one, LinearMap.id_apply] at h1
    have h2 : evM (1 : Matrix (Fin N) (Fin N) ℂ) (0 : MvPolynomial (Fin N × Fin N) ℂ) = 0 := by simp [evM]
    rw [h2] at h1
    exact hv0 (inner_self_eq_zero.mp h1.symm)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hF0
  have hnn : ∀ s, 0 ≤ μ s + K := fun s => by
    rw [← Fq_deg hP v0 μ K htor v0 m0 hm0 s]
    positivity
  refine ⟨fun s => (μ s + K).toNat, Fl hP v0, fun s => Int.toNat_of_nonneg (hnn s), ?_, hF0, ?_⟩
  · intro x
    rw [Fl_apply, dualWeylPoint ℂ N N _ _]
    refine ⟨?_, fun l j hlj c => Fq_colAdd hP v0 hlow l j hlj c x⟩
    intro m hm
    funext s
    rw [weight_colW]
    have h1 := Fq_deg hP v0 μ K htor x m hm s
    have h2 := Int.toNat_of_nonneg (hnn s)
    omega
  · intro g x
    rw [Fl_apply, Fl_apply]
    exact Fq_intertwine hP v0 g x
end PI.WMI
