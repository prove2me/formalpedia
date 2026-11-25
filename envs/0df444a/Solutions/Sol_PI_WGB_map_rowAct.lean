-- Prove2me | solution 1 for PI.WGB.map_rowAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:09.22309+00:00
-- url     : https://prove2.me/submissions/2857dc75-f026-4b28-91e7-5ce5da3371d0

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
namespace PI.WGB
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r c : ℕ}
    (A : Matrix (Fin r) (Fin r) R) (p : MvPolynomial (Fin r × Fin c) R) :
    map φ (rowAct R A p) = rowAct S (A.map φ) (map φ p) := by
  have : (map φ).comp (rowAct R (n := c) A).toRingHom =
      (rowAct S (n := c) (A.map φ)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [rowAct]
    · intro v; simp [rowAct]
  exact congrArg (fun ψ => ψ p) this
end PI.WGB
