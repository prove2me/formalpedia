-- Prove2me | solution 1 for PI.WGB.rowAct_comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:39.70629+00:00
-- url     : https://prove2.me/submissions/c485432f-1d58-4a35-9ca5-ba293d61d6de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_Formalism_UG_P_wlocal_rowAct_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution {R : Type} [CommRing R] {r c : ℕ} (A B : Matrix (Fin r) (Fin r) R)
    (p : MvPolynomial (Fin r × Fin c) R) : rowAct R B (rowAct R A p) = rowAct R (A * B) p := by
  rw [Formalism.UG.P.wlocal_rowAct_mul]; rfl
end PI.WGB
