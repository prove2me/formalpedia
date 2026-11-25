-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.hform_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:36.251795+00:00
-- url     : https://prove2.me/submissions/4d154ed6-c66b-4818-a12a-ca43086b353e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_hform_add_right
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
open NumberField Matrix Formalism.UG PI.InHHClassFin
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {A : Type} [CommRing A] {n ι : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x : n → A) (s : Finset ι) (y : ι → n → A) :
    hform σ J x (∑ i ∈ s, y i) = ∑ i ∈ s, hform σ J x (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hform]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right, ih]
end PI.UnitaryGroupMassFormula.InHHClassFin
