-- Prove2me | solution 1 for PI.WGB.isUU_E_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:32.76564+00:00
-- url     : https://prove2.me/submissions/26c85f68-27af-43c6-8daa-7dbaa382425f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
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
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}
namespace PI.WGB
theorem _root_.solution (a b : Fin n) (hab : a < b) (c : ℂ) :
    IsUU (Formalism.UG.P.wlocal_E b a c).conjTranspose := by
  refine ⟨fun i j' h => ?_, fun i => ?_⟩
  · simp only [Matrix.conjTranspose_apply, Formalism.UG.P.wlocal_E]
    rw [if_neg (by intro e; subst e; exact lt_irrefl _ h), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩; exact lt_asymm h hab
  · simp only [Matrix.conjTranspose_apply, Formalism.UG.P.wlocal_E, if_true]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h2⟩; exact lt_irrefl _ (h2 ▸ hab)
end PI.WGB
